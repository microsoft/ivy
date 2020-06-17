
Specifying and testing TCP
==========================

We will write a wire specification of TCP, and then try to test the
Linux implementation of TCP against this specification. The
specification is in the file `tcp_spec.ivy`. Read through the
specification and make sure you understand what the specification
state variables represent (even if the state update logic isn't
clear). 

The test setup uses the virtual networking capabilities of Linux.  A
TCP server using the Linux TCP stack is set up on the virtual
interface 10.0.0.1. This is connected via a virtual Ethernet to
interface 10.0.0.2, where we run the tester. We set it up this way
because we *don't* want the Linux TCP stack to be running on the same
interface as our tester, since they would interfere with each other.

Since we need some application on the server side, we will use an echo
server (see `echo.c`). This simple program just opens up a TCP port,
accepts connections and echoes back the data sent to it.

For details on how to set up and run a test, see `TCP_setup.md`.

TCP example trace 1
-------------------

The file `tcp_trace_1.png` contains a screenshot of Wireshark, showing
packets on the virtual Ethernet between the tester and echo
server. The tester is using port 1235 while the echo server is using
port 1242. Let's run through this trace to see how it is generated.

The first IP packet is actually unrelated to our test. It is Linux
trying to close a previous connection using a FIN segment. Our tester
ignores this packet.

In packet 2, the tester sends a SYN segment, beginning a new
connection. It can only do this, since initially it is in an
unsynchronized state. The server responds with SYN/ACK. The tester the
resends SYN in packet 4. This is allowed by the specification, because
it allows the client to silently transition back to the CLOSED state.
However, it seems reasonable that retransmission of SYN should be
allowed anyway in the SYN-SENT state, after a timeout, even though
this is not shown in the state diagram. Does the RFC say anything
specific about this?

The server responds to this retransmission by resending SYN/ACK. Again
this is reasonable, but is it explicit allowed in the RFC? Then in
packet 6, the tester sends ACK to the server's SYN/ACK. Notice the
sequence number and ack number in this packet. Where are these
determined in the spec?

In packet 8, the tester sends a byte of data (notice Len=1). The
server then sends ACK. Notice the ack number field of this
packet. What has changed in the protocol state to allow this increase?

The tester sends two more data bytes, then sends FIN/ACK in
packet 14. Notice the sequence number (one after the last byte, the
location of the FIN marker). The server sends back FIN/ACK. Notice the
ACK number (one past the FIN marker). Where is this determined in the
spec? In packet 17, the tester sends ACK twice, but notice that this
ACK is not for the FIN. Why?

At packet 19, the tester resends FIN/ACK, along with the last byte of
data. You might ask why the tester is allowed to resend a data byte
that has already been acked. This is because the reception and
processing of the ACK is invisible to the spec. Thus, we have to assume
the ACK might have been dropped or delayed (as the server also must).

Finally at packet 21, the tester sends ACK for the server's FIN. How
do we know this is the ACK for the FIN? At this point the connection
is closed, since both ends have received ACK for their FIN segments.

The server then opens a new connection at sequence number 0 by sending
SYN in packet 22. This is allowed because the previous ack allowed us
to move back to the CLOSED state. After a fair number of resends of
SYN, something funny happens. The tester sends SYN with a different
sequence number. This means it has silently gone back to the CLOSE
state and started a new connection. However, such a SYN could also be
seen if a delayed SYN segment from a previous connection were
received.  Then notice how the server responds: it sends ACK for the
original SYN in packet 32. The tester flags this as a specification
violation:

    tcp_spec.ivy: line 259: error: assertion failed

Here is the violated requirement:

    require dg.ack & ~dg.syn -> ackable(d,s,dg.ack_num_field);
    
The spec was expecting SYN/ACK but instead got ACK. Is this OK? Let's
see what RFC 793 says (page 36).

    If the connection does not exist (CLOSED) then a reset is sent
    in response to any incoming segment except another reset.
    
Since the connection is not CLOSED this does not apply.

    If the connection is in any non-synchronized state (LISTEN,
    SYN-SENT, SYN-RECEIVED), and the incoming segment acknowledges
    something not yet sent (the segment carries an unacceptable ACK),
    ...  a reset is sent.

Again, does not apply, since there was no ACK.

    If the connection is in a synchronized state (ESTABLISHED,
    FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT, CLOSING, LAST-ACK, TIME-WAIT),
    any unacceptable segment (out of window sequence number or
    unacceptible acknowledgment number) must elicit only an empty
    acknowledgment segment containing the current send-sequence number
    and an acknowledgment indicating the next sequence number expected
    to be received, and the connection remains in the same state.
    
Again, does not apply, since the server is not in a synchronized state
(it is in SYN-RCVD).

So what should the server do if it is in SYN-RCVD and it gets an
unacceptable segment (in this case, one with a bad sequence number)?
The RFC doesn't seem to say. Linux seems to have extended the above
paragraph to apply to the SYN-RCVD state. Is that reasonable? Should
we modify the spec to allow it? If so, how should we modify the spec?
Should we allow an empty ack to occur at any time in the SYN-RCVD
state? Should we add a state variable to record the fact that a bad
segment has been received and allow the empty ack only in this case?
What do other TCP implementations do in this case?

TCP example trace 2
-------------------

The screenshot in `tcp_trace_2.png` shows a case where, in response to
SYN/ACK, the client (i.e., the tester) sends FIN/ACK with one byte of
data (packet 25). This can happen because the ACK sent by the client
could be delayed or dropped.  The server, in the SYN-RCVD state, sends
back ACK (packet 26) with a byte of response data, then sends FIN/ACK
(packet 27). Is this correct? How can we explain it in terms of the
RFC?

Consider the SYN-SENT state in the state diagram on page 23 of the
RFC. On receiving the SYN/ACK sent by the peer, it sends ACK and goes
to the ESTABLISHED state. From this point it can close and send
FIN. But what happens if the packets are re-ordered so that the FIN
arrives before the ACK? The server will receive FIN in the SYN-RCVD
state, as in the screenshot.  The state diagram doesn't say what
happens in this case. In the Ivy spec, we say (at line 474 of
`tcp_spec.ivy`) that the peer should go into the CLOSE-WAIT state
(that is, synchronized with `finned = true`). This seems to be what
Linux has done (i.e., it waited for the echo server to call `close`
and then sent FIN). Does the RFC text say anything about this case?
Should we instead ignore the FIN and stay in the SYN-RCVD state
waiting for ACK, as the state diagram seems to imply?


Fixing trace 1
--------------

The spec was modified to allow the passive TCP (the server) to send an
empty ACK from the SYN-RCVD state, so long as it matches the SYN/ACK.
Here is the change:

    require dg.ack & ~dg.syn -> ackable(d,s,dg.ack_num_field)
        | synackable(d,s,dg.ack_num_field) & syn_rcvd(s,d);  # <---new!

Is this OK? It seems like this is reasonable, since an old SYN can always arrive
in this state, which triggers Linux to send empty ACK. But what hppens to the client
when it receives empty ACK? What if the empty ACK arrives first? Does it send RST?
To find out, we'll have to test the client.

TCP example trace 3
-------------------

In sreenshot in `tcp_trace_3.png` we are testing the Linux TCP client
(i.e., active mode TCP). The program being tested is `ohce.c`. The
client is port 1236 and the tester (the server) is port 1235. After
sending packet 9, the client should have gone into the TIME-WAIT
state. At this point the tester continues to send ACKS and a repeat FIN/ACK. 
The client responds with ACK. Is this OK? The spec says:

    If the connection is in a synchronized state (ESTABLISHED,
    FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT, CLOSING, LAST-ACK, TIME-WAIT),
    any unacceptable segment (out of window sequence number or
    unacceptible acknowledgment number) must elicit only an empty
    acknowledgment segment... 
    
Was the repeat FIN/ACK an unacceptable segment? Why?

The trouble with our spec here, assuming that the ACK is OK, is that
it expects the client to go into the CLOSED/LISTENING states after
sending its ACK for the server's FIN, but actually it stays in
TIME-WAIT for a while. Probably this needs to be fixed. I fixed it
by removing the commented lines below:

                if finacked(s,d) & finacked(d,s) {
                    listen(s,d) := true;
                    closed(s,d) := true;
                    listen(d,s) := true;
                    closed(d,s) := true;
    #               synchronized(s,d) := false;
    #               finned(s,d) := false;
    #               finacked(s,d) := false;
                };

What this means is that the sender of the final ACK does not leave the
synchronized state immediately, but it can silently go to CLOSED or
LISTEN.

TCP example trace 4
-------------------

In sreenshot in `tcp_trace_4.png` we are again testing the Linux TCP
client. In this case, we start with the triple handshake, then the
client sends 5 bytes.  The server acknowledges and sends 1 byte. The
client acks this byte then sends FIN/ACK.  The client acks the
FIN. Then the server sends FIN/ACK, but notice the the ACK numbher
does not include the client's FIN marker. So in other words, what has
happened here is that the client and server have sent FIN/ACK in
parallel. However, the server's FIN/ACK has been delayed, so that its
ACK of the client's FIN arrives first. Then the client responds with
RST!

It seems like the client is wrong here, because it should only respond
with RST when an ACK is definitely wrong, but here the FIN/ACK is fine
-- it just got delayed. What do you think? Is this a Linux bug?

By the way, this trace got an assertion failure here:

    # A TCP may send RST in the SYN_RCVD, SYN_SENT, LISTEN and CLOSED states

    require dg.rst -> syn_rcvd(s,d) | syn_sent(s,d) | listen(s,d) | closed(s,d);

That is, the client sent RST when it should have been in a
synchronized state, since it never acked the server's FIN. But is this
specification correct? Should RST be allowed in synchronized states?

TCP example trace 5
-------------------

In `tcp_trace_5.png`, we are testing the Linux TCP client. AT packet
7, the client sends FIN/ACK.  The server sends FIN/ACK at
packet 8. The client ACKs this, then repeats its FIN/ACK. The server
ACK's this at packet 11 (and again many times). But the client never
leaves the TIME-WAIT state and goes back to startiong a new
connection. Why is that? Does it keep resetting the timer, so that the
timer never actually expires. This trace goes on wquite a while -- the full
trace is in `tcp_trace_5.pcapng`.

TCP example trace 6
-------------------

This trace (`tcp_trace_6.png`) sheds some further light on the RST in
trace 4.  The client sends FIN/ACK. This is not ACKed by the server,
whiich then sends some more data. But there's nothing wrong with this,
since the data could have been sent before the FIN/ACK from the client
was received. So why is RST sent? 

TCP example trace 7
-------------------

This trace was obtained by preventing the tester from sending any more
data after receiving FIN to prevent the problem of traces 4 & 6. Also,
after both FIN's have been ACKed, we forbid the tester ro sending any
packets, until the next SYN. In this way, the problem of getting stick
in TIME-WAIT as in trace 5 is avoided. Now we see a long trace that
runs through a number of connections. Notice in some places (e.g.,
packet 12) there is a long delay (almost 60s). THis must be the 2MSL
delay in the TIME-WAIT state. This delay should only occur in a TCP if
it initiated FIN. Is that true in this trace? The full trace is in
`tcp_trace_7.pcapng`, which you can load into Wireshark.


Exercise
--------

Try to construct a full state diagram for Linux TCP. The state diagram
should include all messages that can be sent and received in each
state and be consistent with the traces we have seen thus far. Also
consider important message cases such as whether the ACK number is
expected. Are there cases we still can't fill in (i.e., responses to
certain messages in certain states)? What experiment would we need to
perform to fill in those cases?

TCP example trace 8
-------------------

This trace, `tcp_trace_8.png`, shows the Linux TCP client sending more
that one segment's worth of data. Notice the Linux TCP sends PSH only
under a specific circumstance. Is this something that should be part
of the spec, or is it Linux-specific?

RFC 1122 - Requirements for Internet Hosts - Communication Layers:

    A TCP MAY implement PUSH flags on SEND calls.  If PUSH flags
    are not implemented, then the sending TCP: (1) must not
    buffer data indefinitely, and (2) MUST set the PSH bit in
    the last buffered segment (i.e., when there is no more
    queued data to be sent).

TCP example trace 9
-------------------

This trace, `tcp_trace_9.png`, shows the Linux TCP client sending 512
bytes at a time and sleeping for one second between send calls, so
that TCP using Nagle's algorithm will actually send the data. Notice
that each time Linux TCP sends 512 bytes (even for resends) it sets
the PSH bit.  This is because it always sets the PSH bit when its
buffer becomes empty.  Question: can we specify this only looking at
the wire (i.e., the protocol level)? Or do we need to also see the app
level events? 

TCP example trace 10
--------------------

This trace, `tcp_trace_10.png` and `tcp_trace_10.pcapng`, shows the
Linux TCP client sending FIN at packet 40. The tester, taking the
passive role, waas constrained not to send FIN. The TCP parameter
`tcp_fin_timeout` was set to 5 seconds (see `man tcp`). Notice that
the tester keeps sending ACK but never sends FIN. Linux times out at
packet 64 and sends SYN. The next ACK received from the tester causes
RST, because the ACK number is unexpected. This shows that Linux does
time out after sending FIN but not receiving FIN for 5 seconds, as `man tcp`
suggests. 

Here's what ivy says after receiving the RST:

    assertion_failed("tcp_spec.ivy: line 238")
    tcp_spec.ivy: line 238: error: assertion failed

At line 238 it says:

    require dg.syn & ~dg.ack -> closed(s,d) | listen(s,d) | syn_sent(s,d);

That is, Linux should have been in state FINWAIT-2, so it shouldn't
have sent SYN, but it has gone back to CLOSED. So the specification
violation menitoned in `man tcp` was detected.





 








