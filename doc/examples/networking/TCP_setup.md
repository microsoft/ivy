
Setup
=====

We will test the Linux implementation of TCP, using a virtual
network. Here is the setup:

    echo                virtual link               
    server 10.0.0.1        <--->         10.0.0.2 tester
    
This test setup is not ideal, since we can't control or observe the
upper interface of the server. The problem is that the tester lives in
a virtual network domain, so it doesn't have access to both ends of
the link. For UDP, we got away with both sending and revceiving on the
loopback interface. However, TCP differs from UDP in that it responds
on ports it is not listening on (with RST). This means that TCP
interferes with our tester, so we have to run the tester on a
different (virtual) network.

Set up virtual network interfaces:

    sudo ./vnet_setup.sh start
    
Compile the echo server if needed:

    gcc echo.c -o echo
    
Start an echo server on port 1234 in another terminal:

    ./echo 1234


Compile the tester:

    ./tcp_test_compile.sh
    
You may need to enter your password to do this, since it requires root
priviledges to enable access to raw ethernet frames. If the `setcap` command
fails, your OS may not support the necessary capabilities. In this case you
need to run the tester as root -- use the script `tcp_test_root.sh` instead of
`tcp_test.sh` below.

Start wireshark and observe the traffic on veth0:

    sudo wireshark &

Run the tester from the remote virtual address.

    ./tcp_test.sh
    
You can add some options to this command:

- `server_port=XXX`: The port number that you ran the echo server on
- `seq0=XXX`:  The starting sequence number of the client

Issues:

1) See trace `unexpected_syn_ack.iex` amd the Wireshark screenshot. At line 4 of the screenshot, the server sends out an ACK from state SYN_RCVD. Is that OK?  

2) See trace `unexpected_syn_ack.iex` amd the Wireshark screenshot.  Here, a connection is established. The tester sends a buch of empty segments, some with SYN, some with ACK. Most of these are ignored. One gets a courtesy ACK. Then at some point the server sends out a burst of SYN/ACK segments. Why?

3) Sometimes, if you close the server and restart it, when it gets a SYN with the same sequence number as before, it returns a dupliate ACK from the old connection. That is...

    client                               server
    SYN_SENT  ---> SYN(seq=0) --->       LISTEN
    ???       <--- ACK(ack=7) <---
    
Why? Is it because the sender hasn't observed the "quiet time"? Does the RFC say to do this?

4) What happens if you receive FIN in SYN-RCVD state? This is
possible, since FIN could race ACK. Should you ignore the FIN and
continue to wait for ACK, or should you go to CLOSE-WAIT?

