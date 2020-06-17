#/bin/bash

rem_idx=`sudo ip netns exec TEST su $USER -c 'cat /sys/class/net/veth1/ifindex'`
loc_mac=0x`sed -e s/://g  /sys/class/net/veth0/address`
echo Using rem_idx=$rem_idx and loc_mac=$loc_mac
sudo ip netns exec TEST ./tcp_test host_intf=$rem_idx router_mac=$loc_mac $*



