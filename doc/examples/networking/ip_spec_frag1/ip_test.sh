#/bin/bash

idx1=`cat /sys/class/net/eth0/ifindex`
idx2=`cat /sys/class/net/eth1/ifindex`
echo Using eth0=$idx1 and eth1=$idx2
./ip_test host_intf1=$idx1 host_intf2=$idx2 $*



