import logging
import random
from struct import pack
from zlib import crc32

from pox.core import core
from pox.lib.util import dpidToStr
import pox.openflow.libopenflow_01 as of
from pox.lib.revent import EventMixin
from pox.lib.packet.ipv4 import ipv4
from pox.lib.packet.udp import udp
from pox.lib.packet.tcp import tcp
from pox.lib.addresses import IPAddr, EthAddr
from pox.lib.packet.ethernet import ethernet, ETHER_BROADCAST
from pox.lib.packet.arp import arp
from pox.lib.util import str_to_bool, dpid_to_str, str_to_dpid
from ripllib.mn import topos

from util import buildTopo, getRouting
import time

log = core.getLogger("HederaController")
# log.setLevel(logging.WARNING)

# Number of bytes to send for packet_ins
MISS_SEND_LEN = 2000

IDLE_TIMEOUT = 10
CAPACITY = 1

FLOW_IDLE_TIMEOUT = 10
FLOW_MEMORY_TIMEOUT = 60


# Borrowed from pox/forwarding/l2_multi
class Switch(object):
    def __init__(self):
        self.connection = None
        self.ports = None
        self.dpid = None
        self._listeners = None

    def __repr__(self):
        return dpidToStr(self.dpid)

    def disconnect(self):
        if self.connection is not None:
            log.debug("Disconnect %s" % (self.connection,))
            self.connection.removeListeners(self._listeners)
            self.connection = None
            self._listeners = None

    def connect(self, connection):
        if self.dpid is None:
            self.dpid = connection.dpid
        assert self.dpid == connection.dpid
        if self.ports is None:
            self.ports = connection.features.ports
        self.disconnect()
        log.debug("Connect %s" % (connection,))
        self.connection = connection
        self._listeners = connection.addListeners(self)

    def send_packet_data(self, outport, data=None):
        msg = of.ofp_packet_out(in_port=of.OFPP_NONE, data=data)
        msg.actions.append(of.ofp_action_output(port=outport))
        self.connection.send(msg)

    def send_packet_bufid(self, outport, buffer_id=None):
        msg = of.ofp_packet_out(in_port=of.OFPP_NONE)
        msg.actions.append(of.ofp_action_output(port=outport))
        msg.buffer_id = buffer_id
        self.connection.send(msg)

    def install(self, port, server_src, mac_src, match, buf=None, idle_timeout=0, hard_timeout=0,
                priority=of.OFP_DEFAULT_PRIORITY):
        msg = of.ofp_flow_mod()
        msg.match = match
        msg.idle_timeout = idle_timeout
        msg.hard_timeout = hard_timeout
        msg.priority = priority
        msg.actions.append(of.ofp_action_nw_addr.set_src(server_src))
        msg.actions.append(of.ofp_action_dl_addr.set_src(mac_src))
        msg.actions.append(of.ofp_action_output(port=port))
        msg.buffer_id = buf
        self.connection.send(msg)

    def install2(self, port, server_dst, mac_dst, match, buf=None, idle_timeout=0, hard_timeout=0,
                 priority=of.OFP_DEFAULT_PRIORITY):
        msg = of.ofp_flow_mod()
        msg.match = match
        msg.idle_timeout = idle_timeout
        msg.hard_timeout = hard_timeout
        msg.priority = priority
        msg.actions.append(of.ofp_action_nw_addr.set_dst(server_dst))
        msg.actions.append(of.ofp_action_dl_addr.set_dst(mac_dst))
        msg.actions.append(of.ofp_action_output(port=port))
        msg.buffer_id = buf
        self.connection.send(msg)

    def install_multiple(self, actions, match, buf=None, idle_timeout=0,
                         hard_timeout=0, priority=of.OFP_DEFAULT_PRIORITY):
        msg = of.ofp_flow_mod()
        msg.match = match
        msg.idle_timeout = idle_timeout
        msg.hard_timeout = hard_timeout
        msg.priority = priority
        for a in actions:
            msg.actions.append(a)
        msg.buffer_id = buf
        self.connection.send(msg)

    def _handle_ConnectionDown(self, event):
        self.disconnect()
        pass


def sep():
    log.info("************************************************")


class MemoryEntry(object):
    """
    Record for flows we are balancing
    Table entries in the switch "remember" flows for a period of time, but
    rather than set their expirations to some long value (potentially leading
    to lots of rules for dead connections), we let them expire from the
    switch relatively quickly and remember them here in the controller for
    longer.
    Another tactic would be to increase the timeouts on the switch and use
    the Nicira extension which can match packets with FIN set to remove them
    when the connection closes.
    """

    def __init__(self, server, first_packet, client_port):
        self.server = server
        self.first_packet = first_packet
        self.client_port = client_port
        self.refresh()

    def refresh(self):
        self.timeout = time.time() + FLOW_MEMORY_TIMEOUT

    @property
    def is_expired(self):
        return time.time() > self.timeout

    @property
    def from_client_to_server(self):
        ethp = self.first_packet
        ipp = ethp.find('ipv4')
        tcpp = ethp.find('tcp')

        return ipp.srcip, ipp.dstip, tcpp.srcport, tcpp.dstport

    @property
    def from_server_to_client(self):
        ethp = self.first_packet
        ipp = ethp.find('ipv4')
        tcpp = ethp.find('tcp')

        return self.server, ipp.srcip, tcpp.dstport, tcpp.srcport


class HederaController(object):

    def __init__(self, t, r, service_ip, servers=[]):
        self.switches = {}  # Switches seen: [dpid] -> Switch
        self.t = t  # Master Topo object, passed in and never modified.
        self.r = r  # Master Routing object, passed in and reused.
        self.macTable = {}  # [mac] -> (dpid, port)
        self.macTable2 = {}
        self.paths = {}
        self.flows = {}
        self.link_usage = {}

        self.service_ip = IPAddr(service_ip)
        self.servers = [IPAddr(a) for a in servers]
        self.live_servers = {}  # IP -> MAC,port
        self.selected_server = None
        try:
            self.log = log.getChild(dpid_to_str(self.con.dpid))
        except:
            # Be nice to Python 2.6 (ugh)
            self.log = log

        self.total_connection = {}  # IP -> total connection
        for ip in servers:
            self.total_connection[ip] = 0
        self.memory = {}  # (srcip,dstip,srcport,dstport) -> MemoryEntry

        self.outstanding_probes = {}  # IP -> expire_time
        # How quickly do we probe?
        self.probe_cycle_time = 5

        # How long do we wait for an ARP reply before we consider a server dead?
        self.arp_timeout = 3

        # TODO: generalize all_switches_up to a more general state machine.
        self.all_switches_up = False  # Sequences event handling.
        core.openflow.addListeners(self, priority=0)

    def _raw_dpids(self, arr):
        "Convert a list of name strings (from Topo object) to numbers."
        return [self.t.id_gen(name=a).dpid for a in arr]

    def _flow_key(self, src_ip, dst_ip):
        return str(src_ip) + "::" + str(dst_ip)

    def _path_key(self, src_sw_name, dst_sw_name):
        return src_sw_name + "::" + dst_sw_name

    def _link_key(self, sw1_name, sw2_name):
        return sw1_name + "::" + sw2_name

    def _do_expire(self):
        """
        Expire probes and "memorized" flows
        Each of these should only have a limited lifetime.
        """
        t = time.time()

        # Expire probes
        for ip, expire_at in self.outstanding_probes.items():
            if t > expire_at:
                self.outstanding_probes.pop(ip, None)
                if ip in self.live_servers:
                    self.log.warn("Server %s down", ip)
                    del self.live_servers[ip]

        # Expire flow
        memory = self.memory.copy()
        self.memory.clear()
        for key, val in memory.items():
            ip = key[0]
            if ip in self.live_servers and val.is_expired:
                # Decrease total connection for that server
                self.total_connection[ip] -= 1
            if not val.is_expired:
                self.memory[key] = val

    def _do_probe(self):
        """
        Send an ARP to a server to see if it's still up
        """
        self._do_expire()

        server = self.servers.pop(0)
        self.servers.append(server)

        r = arp()
        r.hwtype = r.HW_TYPE_ETHERNET
        r.prototype = r.PROTO_TYPE_IP
        r.opcode = r.REQUEST
        r.hwdst = ETHER_BROADCAST
        r.protodst = server
        r.hwsrc = self.mac
        r.protosrc = self.service_ip
        e = ethernet(type=ethernet.ARP_TYPE, src=self.mac,
                     dst=ETHER_BROADCAST)
        e.set_payload(r)
        self.log.debug("ARPing for %s", server)
        msg = of.ofp_packet_out()
        msg.data = e.pack()
        msg.actions.append(of.ofp_action_output(port=of.OFPP_FLOOD))
        msg.in_port = of.OFPP_NONE
        self.con.send(msg)

        self.outstanding_probes[server] = time.time() + self.arp_timeout
        core.callDelayed(self._probe_wait_time, self._do_probe)

    @property
    def _probe_wait_time(self):
        """
        Time to wait between probes
        """
        r = self.probe_cycle_time / float(len(self.servers))
        r = max(.25, r)  # Cap it at four per second
        return r

    def _ecmp_hash(self, packet):
        "Return an ECMP-style 5-tuple hash for TCP/IP packets, otherwise 0."
        hash_input = [0] * 5
        if isinstance(packet.next, ipv4):
            ip = packet.next
            hash_input[0] = ip.srcip.toUnsigned()
            hash_input[1] = ip.dstip.toUnsigned()
            hash_input[2] = ip.protocol
            if isinstance(ip.next, tcp) or isinstance(ip.next, udp):
                l4 = ip.next
                hash_input[3] = l4.srcport
                hash_input[4] = l4.dstport
                return crc32(pack('LLHHH', *hash_input))
        return 0

    def _global_first_fit(self, flow_key, path_key, flow_demand, packet):
        if (flow_key in self.flows and self.flows[flow_key] != -1):
            return self.paths[path_key][self.flows[flow_key]]

        for x, path in enumerate(self.paths[path_key]):
            flow_fits = True
            path_len = len(path)
            for i in range(0, path_len - 1):
                link_key = self._link_key(path[i], path[i + 1])
                reverse_link_key = self._link_key(path[i + 1], path[i])
                if self.link_usage[link_key] + flow_demand > CAPACITY:
                    flow_fits = False
                    break
            if flow_fits:
                for i in range(0, path_len - 1):
                    link_key = self._link_key(path[i], path[i + 1])
                    reverse_link_key = self._link_key(path[i + 1], path[i])
                    self.link_usage[link_key] += flow_demand
                    self.link_usage[reverse_link_key] += flow_demand
                self.flows[flow_key] = x
                return path

        hash_ = self._ecmp_hash(packet)
        choice = hash_ % len(self.paths[path_key])
        path = sorted(self.paths[path_key])[choice]
        return path

    def _get_flow_demand(self, dst_ip):
        suffix = "::" + str(dst_ip)

        num_dst_incoming_flows = 0
        for key in self.flows:
            if key.endswith(suffix):
                num_dst_incoming_flows += 1
        return 1 / num_dst_incoming_flows

    def _install_reactive_path(self, event, out_dpid, final_out_port, packet):
        "Install entries on route between two switches."
        if isinstance(packet.next, ipv4):
            ip = packet.next
            in_name = self.t.id_gen(dpid=event.dpid).name_str()
            out_name = self.t.id_gen(dpid=out_dpid).name_str()
            flow_key = self._flow_key(ip.srcip, ip.dstip)
            path_key = self._path_key(in_name, out_name)
            route = None

            if path_key in self.paths:
                self.flows[flow_key] = -1
                flow_demand = self._get_flow_demand(ip.dstip)
                route = self._global_first_fit(flow_key, path_key, flow_demand, packet)
            else:
                hash_ = self._ecmp_hash(packet)
                route = self.r.get_route(in_name, out_name, hash_, False)

            log.info("route: %s" % route)
            match = of.ofp_match.from_packet(packet)
            for i, node in enumerate(route):
                node_dpid = self.t.id_gen(name = node).dpid
                if i < len(route) - 1:
                    next_node = route[i + 1]
                    out_port, next_in_port = self.t.port(node, next_node)
                else:
                    out_port = final_out_port
                if ip.dstip == self.service_ip:
                    mac, port_s = self.live_servers[self.selected_server]
                    log.info("path to %s , to %s server" % (node_dpid, mac))
                    self.switches[node_dpid].install2(out_port, self.selected_server, mac, match,
                                                      idle_timeout=IDLE_TIMEOUT)
                else:
                    self.switches[node_dpid].install(out_port, self.service_ip, self.mac, match,
                                                     idle_timeout=IDLE_TIMEOUT)

    def _eth_to_int(self, eth):
        return sum(([ord(x) * 2 ** ((5 - i) * 8) for i, x in enumerate(eth.raw)]))

    def _int_to_eth(self, inteth):
        return EthAddr("%012x" % (inteth,))

    def _src_dst_str(self, src_dpid, dst_dpid):
        "Return a hash based on src and dst dpids."
        return crc32(pack('QQ', src_dpid, dst_dpid))

    def _flood(self, event):
        packet = event.parsed
        dpid = event.dpid
        in_port = event.port
        # log.info("flood PacketIn to: %s" % packet)

        t = self.t

        # Broadcast to every output port except the input on the input switch.
        # Hub behavior, baby!
        for sw in self._raw_dpids(t.layer_nodes(t.LAYER_EDGE)):
            # log.info("considering sw %s" % sw)
            ports = []
            sw_name = t.id_gen(dpid=sw).name_str()
            for host in t.down_nodes(sw_name):
                sw_port, host_port = t.port(sw_name, host)
                if sw != dpid or (sw == dpid and in_port != sw_port):
                    ports.append(sw_port)
            # Send packet out each non-input host port
            # TODO: send one packet only.
            for port in ports:
                # log.info("sending to port %s on switch %s" % (port, sw))
                # buffer_id = event.ofp.buffer_id
                # if sw == dpid:
                #  self.switches[sw].send_packet_bufid(port, event.ofp.buffer_id)
                # else:
                self.switches[sw].send_packet_data(port, event.data)
                #  buffer_id = None

    def _pick_server(self, key, in_port):
        """
        Pick a server for a (hopefully) new connection
        """
        if len(self.total_connection) == 0:
            return self.live_servers.keys()[0]
        ipserver = self.total_connection.keys()[0]
        totalconns = self.total_connection[ipserver]
        for x in self.total_connection:
            if self.total_connection[x] < totalconns:
                ipserver = x
                totalconns = self.total_connection[x]
        self.log.debug("server koneksi terkecil adalah: %s" % ipserver)
        return ipserver

    def _handle_packet_reactive(self, event):
        global server
        packet = event.parsed
        dpid = event.dpid
        # log.info("PacketIn: %s" % packet)
        in_port = event.port
        t = self.t

        def drop():
            if event.ofp.buffer_id is not None:
                # Kill the buffer
                msg = of.ofp_packet_out(data=event.ofp)
                self.con.send(msg)
            return None

        # log.info("mactable: %s" % self.macTable)
        self.macTable[packet.src] = (dpid, in_port)
        tcpp = packet.find('tcp')
        if not tcpp:
            arpp = packet.find('arp')
            if arpp:
                # Handle replies to our server-liveness probes
                if arpp.opcode == arpp.REPLY:
                    # log.info("packetin arp : %s" %packet)
                    if arpp.protosrc in self.outstanding_probes:
                        # A server is (still?) up; cool.
                        del self.outstanding_probes[arpp.protosrc]
                        if (self.live_servers.get(arpp.protosrc, (None, None))
                                == (arpp.hwsrc, in_port)):
                            pass
                        else:
                            # Ooh, new server.
                            self.live_servers[arpp.protosrc] = arpp.hwsrc, in_port
                            self.log.info("Server %s port %s up" % (arpp.hwsrc, in_port))
                        if len(self.live_servers) == len(self.servers):
                            self.probe_cycle_time = 500

                return
            # Not TCP and not ARP.  Don't know what to do with this.  Drop it.

        ipp = packet.find('ipv4')
        # Learn MAC address of the sender on every packet-in.
        # log.info("reacPacketIn: %s" % packet)

        if ipp.srcip in self.servers:
            log.info("packetin dri server :%s" % packet)
            if packet.dst in self.macTable2:
                out_dpid, out_port = self.macTable2[packet.dst]
                log.info("instal path S: %s %s" % (out_dpid, out_port))
                self._install_reactive_path(event, out_dpid, out_port, packet)

                log.info("sending to S entry in mactable: %s %s" % (out_dpid, out_port))
                self.switches[out_dpid].send_packet_data(out_port, event.data)

        elif ipp.dstip == self.service_ip:
            log.info("packetin dri client :%s" % packet)
            # Ah, it's for our service IP and needs to be load balanced

            # Do we already know this flow?
            key = ipp.srcip, ipp.dstip, tcpp.srcport, tcpp.dstport
            entry = self.memory.get(key)
            if entry is None or entry.server not in self.live_servers:
                # Don't know it (hopefully it's new!)
                if len(self.live_servers) == 0:
                    self.log.warn("No servers!")
                    return drop()
                # Pick a server for this flow
                server = self._pick_server(key, in_port)
                self.log.debug("Directing traffic to %s", server)
                entry = MemoryEntry(server, packet, in_port)
                self.memory[entry.from_client_to_server] = entry
                self.memory[entry.from_server_to_client] = entry
                self.selected_server = server
                # Increase total connection for that server
                if self.total_connection[server] == 0:
                    self.macTable2[packet.src] = (dpid, in_port)
                    # self._flood(event)
                self.total_connection[server] += 1
            # Update timestamp
            entry.refresh()

            # Set up table entry towards selected server
            mac, port = self.live_servers[entry.server]
            dpid_mac = self._eth_to_int(mac)
            # Insert flow, deliver packet directly to destination.
            if mac in self.macTable:
                out_dpid, out_port = self.macTable[mac]
                log.info("sending to entry gff: %s %s" % (out_dpid, out_port))

                self._install_reactive_path(event, out_dpid, out_port, packet)

                log.info("sending to entry in mactable: %s %s" % (out_dpid, out_port))
                self.switches[out_dpid].send_packet_data(out_port, event.data)
        else:
            self._flood(event)

    # Get host index.
    def dpid_port_to_host_index(self, dpid, port):
        node = self.t.id_gen(dpid=dpid)
        return node.pod * ((self.t.k ** 2) / 4) + node.sw * (self.t.k / 2) + ((port - 2) / 2)

    def _handle_PacketIn(self, event):
        # log.info("Parsing PacketIn.")
        if not self.all_switches_up:
            log.info("Saw PacketIn before all switches were up - ignoring.")
            # log.info("PacketIn: %s" % packet)
            return
        else:
            self._handle_packet_reactive(event)

    def _get_links_from_path(self, path):
        path_len = len(path)
        for i in range(0, path_len - 1):
            link_key = self._link_key(path[i], path[i + 1])
            reverse_link_key = self._link_key(path[i + 1], path[i])
            # if link_key is not in self.link_usage and reverse_link_key is not in self.link_usage:
            self.link_usage[link_key] = 0
            self.link_usage[reverse_link_key] = 0

    def _get_equal_cost_routes(self, src, dst):
        src_host_name = self.t.id_gen(dpid=src).name_str()
        src_sw = self.t.up_nodes(src_host_name)
        assert len(src_sw) == 1
        src_sw_name = src_sw[0]
        dst_host_name = self.t.id_gen(dpid=dst).name_str()
        dst_sw = self.t.up_nodes(dst_host_name)
        assert len(dst_sw) == 1
        dst_sw_name = dst_sw[0]
        all_paths = self.r.get_route(src_sw_name, dst_sw_name, None, True)
        for path in all_paths:
            self._get_links_from_path(path)
        self.paths[self._path_key(src_sw_name, dst_sw_name)] = all_paths

    def _get_all_paths(self):
        t = self.t
        # Install L2 src/dst flow for every possible pair of hosts.
        for src in sorted(self._raw_dpids(t.layer_nodes(t.LAYER_HOST))):
            for dst in sorted(self._raw_dpids(t.layer_nodes(t.LAYER_HOST))):
                self._get_equal_cost_routes(src, dst)

    def _handle_ConnectionUp(self, event):
        sw = self.switches.get(event.dpid)
        sw_str = dpidToStr(event.dpid)
        self.con = event.connection
        self.mac = self.con.eth_addr
        log.info("Saw switch come up: %s", sw_str)
        name_str = self.t.id_gen(dpid=event.dpid).name_str()
        if name_str not in self.t.switches():
            log.warn("Ignoring unknown switch %s" % sw_str)
            return
        if sw is None:
            log.info("Added fresh switch %s" % sw_str)
            sw = Switch()
            self.switches[event.dpid] = sw
            sw.connect(event.connection)
        else:
            log.info("Odd - already saw switch %s come up" % sw_str)
            sw.connect(event.connection)
        sw.connection.send(of.ofp_set_config(miss_send_len=MISS_SEND_LEN))

        if len(self.switches) == len(self.t.switches()):
            log.info("Woo!  All switches up")
            self.all_switches_up = True
            self._get_all_paths()
        if self.all_switches_up == True:
            self._do_probe()


def launch(topo, ip, servers):
    """
    Launch Hedera Controller

    topo is in format toponame,arg1,arg2,...
    """
    # Boot up ARP Responder
    from proto.arp_responder import launch as arp_launch
    arp_launch(eat_packets=False, **{str(ip): True})
    import logging
    logging.getLogger("proto.arp_responder").setLevel(logging.WARN)

    # Instantiate a topo object from the passed-in file.
    if not topo:
        raise Exception("please specify topo and args on cmd line")
    else:
        t = buildTopo(topo, topos)
        r = getRouting('hashed', t)
        servers = servers.replace(",", " ").split()
        servers = [IPAddr(x) for x in servers]
        ip = IPAddr(ip)
    log.info("Load Balancer Ready.")
    core.registerNew(HederaController, t, r, IPAddr(ip), servers)

    log.info("Hedera running with topo=%s." % topo)
