#!/bin/sh

# This scripe uses CORE to set up a virtual network with two nodes n0
# and n1 located respectively at ip addresses 10.0.0.1 and and
# 10.0.0.2.

core-cleanup > /dev/null 2>&1
ip link set vbridge down > /dev/null 2>&1
brctl delbr vbridge > /dev/null 2>&1

# create a server node namespace container - node 0
vnoded -c /tmp/n0.ctl -l /tmp/n0.log -p /tmp/n0.pid > /dev/null
# create a virtual Ethernet (veth) pair, installing one end into node 0
ip link add name rmyveth0 type veth peer name n0.0
ip link set n0.0 netns `cat /tmp/n0.pid`
vcmd -c /tmp/n0.ctl -- ip link set n0.0 name eth0
vcmd -c /tmp/n0.ctl -- ifconfig eth0 10.0.0.1/24 up

# create client node namespace container - node 1
vnoded -c /tmp/n1.ctl -l /tmp/n1.log -p /tmp/n1.pid > /dev/null
# create a virtual Ethernet (veth) pair, installing one end into node 1
ip link add name rmyveth1 type veth peer name n1.0
ip link set n1.0 netns `cat /tmp/n1.pid`
vcmd -c /tmp/n1.ctl -- ip link set n1.0 name eth0
vcmd -c /tmp/n1.ctl -- ifconfig eth0 10.0.0.2/24 up

# bridge together nodes using the other end of each veth pair
brctl addbr vbridge
brctl setfd vbridge 0
brctl addif vbridge rmyveth0
brctl addif vbridge rmyveth1
ip link set rmyveth0 up
ip link set rmyveth1 up
ip link set vbridge up
