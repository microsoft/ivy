---
layout: page
title: Transport Service
---

The distributed hash table service need a reliable transport mechanism
for two reasons.  It's important not to lose parts of the has table in
transit. Moreover, for consistency, we rely on the fact that we never
have two values for the same key on the system. This invariant could be
violated if messages were duplicated.

We will build a [non-duplicating ordered transport
service](trans.ivy). The fact that message delivery is ordered isn't
needed for the sharded hash table protocol, but it makes it easier to
implement reliable non-duplicating transmission.

# Specification

Here is the interface of the transport service:

    module sht_transport(lower,req,shard,seq_num,id) = {

        relation requested(D:id,R:req)
        relation replied(D:id,R:req)
        relation delegated(D:id,S:shard)

        action send_request(src:id,dst:id,rq:req) returns (ok:bool)
        action send_delegate(src:id,dst:id,s:shard)  returns (ok:bool)
        action send_reply(src:id, dst:id, rq:req) returns (ok:bool)
        action recv_request(dst:id,rq:req)
        action recv_reply(dst:id,rq:req)
        action recv_delegate(dst:id,s:shard)

        ...
    }

The `lower` parameter of the module is the low-level network
interface, an unreliable, duplicating message sevice. Parameters `req`
and `shard` are data types for message contents, `seq_num` is a type
of [packet sequence numbers](seqnum.html) and `id` is a type of process id's.

The service has specific calls and call-backs for the three types of
messages in the protocol: request, reply and delegate. The `send` actions
return a Boolean `ok` to indicate the message was successfully enqueued.
This allows for the possibility that the message queues are bounded.

There are three corresponding relations in the abstract state:
`requested`, `replied` and `delegated`. Each indicates that a message
of a given type is in transit to a certain destination. The type `req`
is used for both request and reply messages, while the delegate
message contains a [shard](shard.md).

The service specification has three parts relating to the three types
of messages. Here is the specification for request messages:

        object spec = {

            after init {
                requested(D,R) := false
            }

            before send_request {
                assert ~requested(dst,rq)
            }

            after send_request {
                if ok {
                    requested(dst,rq) := true
                }
            }

            before recv_request {
                assert requested(dst,rq);
                requested(dst,rq) := false
            }
            ...

The specifications for reply and delegate messages are similar.  The
specification does not allow a meesage to be sent if it is already in
transit.  In other words, we cannot have two identical messages in the
network. This might at first seem odd. That is, there is no reason we
cannot have to outstanding request for the same data. Request
operations are unique, however, because each contains a unique
[transaction id](reference.html) as a ghost field.

Notice that `send_request` only records a request in transit
if the return value `ok` is true. A request can only be received if it
is in transit, and when it is received is removed from the set of
requests in transit.

The specifications of the reply and delegation actions are similar,
except for the data types.

# Implementation

To implement the transport service, we need a concrete data type for
messages. We'll us a tagged union with four tags:

        type mtype = {request_t, reply_t, delegate_t, ack_t}

The first three are for our three types of protocol messages and the
last, `ack_t` is for acknowledgment packets. Here is the struct that
holds the messages:

    object net_msg = {
        type t = struct {
            mty : mtype,
            src : id,
            num : seq_num.t,
            rq : req,
            sh : shard
        }
    }

In has a tag `mty`, a source id, a sequence number and two payload
fields: a `req` and a `shard`. This is a little bit wasteful of
network bandwidth, since only one of these two fields is actually
used. When Ivy has built-in support for tagged union types, this waste
can be eliminated. Since we are using a concrete datatype for the
messages, the IVy compiler can generate serializers and
deserializers for messages.  We don't have to write them from
scratch.

Now let's look at the code. We will describe the implementation in the
parameterized style, with one object for each process id. We'll call
this object the *host*.  Each host has set of outgoing message queues,
one per destination host, and each queue has its own timer for
re-transmission:

    object impl(me:id) = {

        instance mq(D:id) : message_queue(net_msg,seq_num)
        instance timer(D:id) : timeout_sec
        

In addition, for each destination, we record `send_seq`, the next
sequence number to use, and for each message source we record
`recv_seq` the next sequence number to receive. Initially, both are zero:

        individual send_seq(S:id) : seq_num.t
        individual recv_seq(S:id) : seq_num.t

        init recv_seq(S) = 0 & send_seq(S) = 0

## Sending

Here is the code that sends requests:

        implement send_request(dst:id,rq:req) {
            local msg : net_msg.t, seq : seq_num.t {
                net_msg.mty(msg) := request_t;
                net_msg.src(msg) := me;
                net_msg.rq(msg) := rq;
                net_msg.num(msg) := send_seq(dst);
                send_seq(dst) := seq_num.next(send_seq(dst));
                ok := mq(dst).enqueue(msg);
                if ok {
                    call lower.send(me,dst,msg)
                }
            }
        }

It starts by constructing packet `msg` by filling in the fields. The
sequence number of the packet is `send_seq` for the specified
destination. Then `send_seq` is incremented and we call the message
queue `mq(dst)` to enqueue the message. Finally, if the message was
successfully enqueued, we call into the low-level network interface to
actually send the message. Notice that the source parameter is `me`, the
id of the host.

Sending messages for replies and delegations is similar.

## Receiving

To receive messages, we implement the `recv` action of the low-level
network interface. Here is the code:

        implement lower.recv(msg:net_msg.t) {
            local src:id,seq:seq_num.t {
                seq := net_msg.num(msg);
                src := net_msg.src(msg);
                if seq <= recv_seq(src) & net_msg.mty(msg) ~= ack_t  {
                    local ack : net_msg.t {
                        net_msg.mty(ack) := ack_t;
                        net_msg.src(ack) := me;
                        net_msg.num(ack) := seq;
                        call lower.send(me,src,ack)
                    }
                };
                if net_msg.mty(msg) = ack_t {
                    call mq(src).delete_all(seq)
                }
                else if seq = recv_seq(src) {
                    recv_seq(src) := seq_num.next(recv_seq(src));
                    if net_msg.mty(msg) = request_t {
                        call recv_request(me,net_msg.rq(msg))
                    }
                    else if net_msg.mty(msg) = reply_t {
                        call recv_reply(me,net_msg.rq(msg))
                    }
                    else if net_msg.mty(msg) = delegate_t {
                        call recv_delegate(me,net_msg.sh(msg))
                    }
                }
            }
        }

Several things are going on here. First we deal with acknowledgments.
We acknowledge a message if its sequence number is less than or equal to
the expected sequence number `recv_seq`. The idea here is that all packets
with lesser sequence numbers have already been received. We have to
acknowledge the packet because the eariler acknowledgment might have been
lost. A greater sequence number will be ignored, since we receive
messages strictly in order.

Next, if the messages is an acknowledgment, we know that all the
messages up to the sequence number of the ack have been received
(again, because reception is ordered). So we delete all the outgoing
messages in the queue with sequence numbers up to the acknowledged
one.

Then we handle payloads. If the message has sequence number
`recv_seq` (the one we are expecting to receive) we increment
`recv_seq` and process the message. We split cases on the message tag
and call the appropriate `recv` action with the appropriate payload
field.

## Timeouts

When a message queue times out, we may need to retransmit a
message. We do this by implementing the `timeout` action of the timer
interface, like this:

        implement timer.timeout(dst:id) {
            if ~mq(dst).empty {
                call lower.send(me,dst,mq(dst).pick_one)
            }
        }

Notice that because the timer is a parameterized object, the `timeout`
action as a parameter corresponding to the destination host id. We
check to see if the corresponding queue is empty. If not, we call
`pick_one` to select a message to re-transmit, and then call the
low-level network service to send the message.

# Proof

The proof of this implementation requires quite a few invariants,
partly because we need similar invariants requests, replies and
delagations.

## Message queue invariants

First, we need to relate the message queue contents to the abstract
state relations that indicate which messages are in transit. For requests,
an enqueued message that is not yet received must correspond to a request
in transit:

    conjecture mq(D).contents(M) & impl(D).recv_seq(me) <= net_msg.num(M)
               & net_msg.mty(M) = request_t -> requested(D,net_msg.rq(M))

Moreover, we can't have unreceived duplicate messages in the network. This is
a bit subtle. We disallow two identical messages in the same queue
(i.e., with distinct sequence numbers). We also have to disallow a message
in transit to the same destination from two distinct sources, since
the abstract state does not distinguish sources:


    conjecture impl(S1).mq(D).contents(M1) & impl(D).recv_seq(S1) <= net_msg.num(M1)
        & impl(S2).mq(D).contents(M2) & impl(D).recv_seq(S2) <= net_msg.num(M2)
        & net_msg.mty(M1) = request_t & net_msg.mty(M2) = request_t 
        & (S1 ~= S2 | net_msg.num(M1) ~= net_msg.num(M2))
           -> net_msg.rq(M1) ~= net_msg.rq(M2)

The above is a bit redundant. It might be better style to define
a relation describing an unreceived request message in a given queue.
We have a similar invariants for replies and delegations.

To make sure we don't create duplicate sequence numbers in the queues,
we need to say that now that the sending sequence number is bigger
than any message in the queue:

    conjecture mq(D).contents(M) -> ~(send_seq(D) <= net_msg.num(M))

No sequence number occurs twice in a queue (this is actually an invariant
of message queues and could have been stated in their implementation):

    conjecture mq(D).contents(M1) & mq(D).contents(M2) & M1 ~= M2
               -> net_msg.num(M1) ~= net_msg.num(M2)

We also need to know that only appropriate messages are enqueued, that
is, messages in a queue have a correct source field and are not
acknowledgments:

    conjecture mq(D).contents(M) -> net_msg.src(M) = me & net_msg.mty(M) ~= ack_t

## Low-level network invariants

We need to relate the messages in transit in the low-level network to
the implemention state. For non-acknowledgment messages, we need to
know three things:

First, a message intransit must match any queue entry with the same sequence number:

    conjecture lower.spec.sent(M,D) & net_msg.src(M) = me
               & mq(D).contents(M2) & net_msg.num(M2) = net_msg.num(M)
               & net_msg.mty(M) ~= ack_t -> M = M2

Second, a low-level message that hasn't been received yet must still be in the
corresponding queue:

    conjecture lower.spec.sent(M,D) & net_msg.src(M) = S
               & impl(D).recv_seq(S) <= net_msg.num(M) & net_msg.mty(M) ~= ack_t
               -> impl(S).mq(D).contents(M)

Third, every low-level message as actually been sent:

    conjecture lower.spec.sent(M,D) & net_msg.src(M) = me & net_msg.mty(M) ~= ack_t
                -> ~(send_seq(D) <= net_msg.num(M))

Taken together, these properties say that the unreceived low-level
messages are a subset of the messages in the appropriate outgoing
queue.

Finally, we need to know that low-level acknowledgment packets are correct. This means
that any acknowledged sequence number must actually have been received:

    conjecture lower.spec.sent(M,D) & net_msg.src(M) = S
               & net_msg.mty(M) = ack_t -> ~(impl(S).recv_seq(D) <= net_msg.num(M))

Together, these invariants are inductive and are sufficient to show
the implementation is correct in the sense of delivering each sent
protocol message no more than once.

## The message queues

We aqlso need to verify the mesage queues agains their specification. We will use [parameter stripping](leader.md) to do that:

    isolate iso_mq(mq_me:id) = mq(mq_me) with seq_num
        
What this means is that we verify one message queue instance named
`mq_me` in isolation from the others. This works because the different
message queues don't interfere with each other.

# Testing

Before implementing the application-level protcol on top of this
service, it's worth instantiating and proving it, and perhaps also
testing it a bit. Here is a [test module](trans_test.ivy):

    include trans
    include seqnum
    include udp

    type id
    type req
    type shard

    instance seq_num : sequence_numbers

    instance t : sht_transport(u,req,shard,seq_num,id)

    instance u : udp_simple(id,t.net_msg.t)


    isolate iso_t = t.impl with t,u,seq_num

    export t.send_request
    export t.send_delegate
    import t.recv_request
    import t.recv_delegate


We left the `req` and `shard` types uninterpreted, since these don't
matter to the transport service.  We use `udp_simple` as the low-level
datagram service. Let's verify this module:

    ivy_check trans_test.ivy 
    Checking isolate iso_t...
    trying ext:t.impl.timer.timeout...
    checking consecution...
    trying ext:t.send_delegate...
    checking consecution...
    trying ext:t.send_request...
    checking consecution...
    trying ext:u.recv...
    checking consecution...
    Checking isolate seq_num.iso...
    trying ext:seq_num.iter.create...
    checking consecution...
    trying ext:seq_num.iter.end...
    checking consecution...
    trying ext:seq_num.next...
    checking consecution...
    Checking isolate t.impl.iso_mq...
    trying ext:t.impl.mq.delete_all...
    checking consecution...
    trying ext:t.impl.mq.empty...
    checking consecution...
    trying ext:t.impl.mq.enqueue...
    checking consecution...
    trying ext:t.impl.mq.pick_one...
    checking consecution...
    OK

Notice the IVy actually verified three isolates: `iso_t` (the
transport module), `seq_num.iso` (the sequence number module) and
`t.impl.iso_mq` (the parameter-stripped message queue module).

## Compile and run

Let's compile to a REPL and try a few packets:

    $ make -B trans_test
    ivy_to_cpp target=repl isolate=iso_impl trans_test.ivy
    g++ -g -o trans_test trans_test.cpp

    ./trans_test
    > t.send_request(0,1,42)
    true    
    > t.recv_request(1,42)
    t.send_delegate(1,0,66)
    true
    > t.recv_delegate(0,66)
    ...

Notice the order of events. We call `send_request`, which responds with `true`
meaning the pack was sent. Then asynchronously the packet arrives, which results
in a callback of `recv_request`. Also notice we entered integers for message
payloads. The compiler uses machine integers to implement the uninterpreted types,
though logically any type would work.

As an excercise, you might try stripping the first parameter to
generate a parallel implementation. Check that if you send a
message to a process that hasn't started yet, the packet is retried
until that process starts.