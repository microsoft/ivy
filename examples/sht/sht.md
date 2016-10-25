---
layout: page
title: Final Assembly
---

Now we [put all the components together]() to compile a protocol
implementation we can run. First we have to instantiate the modules we have created so far:

    include proto
    include reference
    include key
    include trans
    include udp
    include shard
    include seqnum

    type id
    type data

    instance ref : sht_reference(id,key,data)
    instance shard : table_shard(key,data)
    instance num: sequence_numbers
    instance proto(X:id) : sht_protocol(X,ref,trans,id,key,data,shard)
    instance trans : sht_transport(udp,proto.req.t,shard.t,num,id)
    instance udp : udp_simple(id,trans.net_msg.t)

Notice that the protocol module is instantiated with a paremeter
`X:id`. This creates one process for each process id. We instantiate
`trans` and `udp` after `proto` because of a technicality: IVy allows
forward references to objects but not to types. Since we need
`proto.req.t` (the request message type) in `trans` and
`trans.net_msg.t` (the low-level message type) in `udp`, we have to
instantiate them in this order (or, of course, predefine these types).

Now we actually prove the protocol. We use three isolates for this:

    isolate iso_p = proto with ref,trans,key,shard
    isolate iso_dm(me:id) = proto.impl.dm(me) with key
    isolate iso_hash(me:id) = proto.impl.hash(me) with key,shard

The first verifies the protocol itself. The other two verify the
delegation map and the hash table inside `proto` using parameter
stripping. We need to do this since IVy doesn't yet allow isolates
within parameterized objects. The idea here is that, since the
delegation maps and hash tables of the different processes are
independent, we can verify just one with a symbolic parameter value
`me`. 

We also need to export the protocol's interface actions to the environment:

    export proto.set
    export proto.get
    export proto.delegate_
    import proto.answer

Notice the `answer` is a call-back and therefore an import.

# Proof checking

Before compiling, let's check the whole proof:

    $ ivy_check  sht.ivy
    Checking isolate iso_dm...
    trying ext:proto.impl.dm.get...
    checking consecution...
    trying ext:proto.impl.dm.set...
    checking consecution...
    Checking isolate iso_hash...
    trying ext:proto.impl.hash.extract_...
    checking consecution...
    trying ext:proto.impl.hash.get...
    checking consecution...
    trying ext:proto.impl.hash.incorporate...
    checking consecution...
    trying ext:proto.impl.hash.set...
    checking consecution...
    Checking isolate iso_p...
    trying ext:proto.delegate_...
    checking consecution...
    trying ext:proto.get...
    checking consecution...
    trying ext:proto.set...
    checking consecution...
    trying ext:shard.arr.get...
    checking consecution...
    trying ext:trans.recv_delegate...
    checking consecution...
    trying ext:trans.recv_reply...
    checking consecution...
    trying ext:trans.recv_request...
    checking consecution...
    Checking isolate key.iso...
    trying ext:key.iter.create...
    checking consecution...
    trying ext:key.iter.end...
    checking consecution...
    Checking isolate num.iso_props...
    trying ext:num.iter.create...
    checking consecution...
    trying ext:num.iter.end...
    checking consecution...
    trying ext:num.next...
    checking consecution...
    Checking isolate shard.index.iso...
    trying ext:shard.index.next...
    checking consecution...
    Checking isolate trans.impl.iso_mq...
    trying ext:trans.impl.mq.delete_all...
    checking consecution...
    trying ext:trans.impl.mq.empty...
    checking consecution...
    trying ext:trans.impl.mq.enqueue...
    checking consecution...
    trying ext:trans.impl.mq.pick_one...
    checking consecution...
    Checking isolate trans.iso...
    trying ext:trans.impl.timer.timeout...
    checking consecution...
    trying ext:trans.send_delegate...
    checking consecution...
    trying ext:trans.send_reply...
    checking consecution...
    trying ext:trans.send_request...
    checking consecution...
    trying ext:udp.recv...
    checking consecution...
    OK

Yikes, that's a lot of checking. IVy grinds it out in less than a
minute, however, using the power of
[Z3](https://github.com/Z3Prover/z3).

# Compile and run

To actually run, we'll need to interpret the process id type:

    object impl = {
        interpret id -> bv[1]
    }

We could also interpret the type `data` (the directory values) but
just for testing, the compiler's default interpretation `int` will do.
We create an extract:

    extract iso_impl(me:id) = key,shard,num,trans.impl(me),proto.impl(me),udp.impl(me)

Notice the extract is parameterized. We want to compile a binary
implementing just one host. The implementations that have a host id
parameter are therefore stripped.  The `key`, `shard` and `num`
objects aren't stripped because they are stateless.

We compile:

    $ make sht
    ivy_to_cpp target=repl isolate=iso_impl sht.ivy
    g++ -g -o sht sht.cpp

Since our process id type is `bv[1]` (one-bit binary numbers) we have two process ids.
We fire up terminals A and B, and run the two process:

    A: $ ./sht 0
    A: > 

    B: $ ./sht 1
    B: >

Remember that process `0` is the master which initially owns all the
keys. Let's do some local operations:

    A: > proto.get(7)
    A: true
    A: > proto.answer(7,0,0)
    A: proto.set(7,42)
    A: true
    A: > proto.answer(7,42,0)
    A: proto.get(7)
    A: true
    A: > proto.answer(7,42,0)

So we can get and set values locally. Let's try remotely from process 1:

    B: > proto.get(7)
    B: true
    B: > proto.answer(7,42,0)
    B: proto.set(7,66)
    B: true
    B: > proto.answer(7,66,0)

    A: proto.get(7)
    A: true
    A: > proto.answer(7,66,0)

So we can get and set values remotely. Let's try delegating a shard:

    A: proto.delegate_(1,{is_end:false,val:2},{is_end:false,val:12})
    A: true
    A: > proto.get(7)
    A: true
    A: > proto.answer(7,66,0)

    B: proto.get(7)
    B: 0
    B: > proto.answer(7,66,0)

This looks good, but it's bit hard to tell if the delegation actually
did anything, since the answers don't change. 

# Debug monitoring

It would be nice to be able to observe the packets being exchanged to
see if the expecting things are happening. There's an easy way to do
this: compile in a debug monitor. Here's an example:

    object debug = {
        action send(dst:id,m:trans.net_msg.t)
        action recv(dts:id,m:trans.net_msg.t)
        before udp.send(src:id,dst:id,msg:trans.net_msg.t) {
            call send(dst,msg)
        }
        before udp.recv(dst:id,msg:trans.net_msg.t) {
            call recv(dst,msg)
        }
    }
    import debug.send
    import debug.recv

This monitor synchronizes with the low-level message receive and send
calls `udp.send` and `udp.recv`. In each case it just calls back to the environment,
passing the destination address and message as parameters. 

Now we have to add the object `debug` to our extract so it doesn't get
abstracted away:

    extract iso_impl(me:id) = key,shard,num,trans.impl(me),proto.impl(me),udp.impl(me),debug(me)

Let's run this extract:

    A: ./sht 0
    A: > proto.get(7)
    A: debug.send(0,{mty:reply_t,src:0,rq:{src:0,rkey:7,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: true
    A: > debug.recv({mty:reply_t,src:0,rq:{src:0,rkey:7,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.send(0,{mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: proto.answer(7,0,0)
    A: debug.recv({mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})

That's a lot just to get the value of key 7 locally. What happened
here? It looks like process 0 handled the request locally, then sent a
reply message to itself for key 7 with value 0. It then recieved the
reply from itself, sent back an acknowledgment to itself, and
presented the answer. Finally, it received the acknowledgment from
itself.

This seems a bit roundabout for a purely local transaction. Might it
make more sense to call back immediately without sending and receiving
a message? The answer is probably not. If we called back to `answer`
from within `get`, the caller would have to deal with the possible
interference caused by `answer`. Probably it's better from a usability
point of view to stash the answer in a message and present it
asynchronously, as if the operation were done remotely. 

Now let's try a remote operation:

    B: > proto.set(7,66)
    B: debug.send(0,{mty:request_t,src:1,rq:{src:1,rkey:7,rtype:1,rdata:66,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: true
    B: > debug.recv({mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: debug.recv({mty:reply_t,src:0,rq:{src:1,rkey:7,rtype:1,rdata:66,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: debug.send(0,{mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: proto.answer(7,66,0)

    A: debug.recv({mty:request_t,src:1,rq:{src:1,rkey:7,rtype:1,rdata:66,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.send(1,{mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.send(1,{mty:reply_t,src:0,rq:{src:1,rkey:7,rtype:1,rdata:66,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.recv({mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:0,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})

From the point of view of process 1, we send a request, get an
acknowledgment, then a reply, then acknowledge the reply, then
answer. From the point of view of process 0, we receive a request,
acknowledge it, send a reply, then receive an acknowledgment for the
reply.

Let's try to delegate:

    A: proto.delegate_(1,{is_end:false,val:2},{is_end:false,val:12})
    A: debug.send(1,{mty:delegate_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:2},hi:{is_end:0,val:12},pairs:[{p_key:7,p_value:66}]}})
    A: true
    A: > debug.recv({mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})

    B: debug.recv({mty:delegate_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:2},hi:{is_end:0,val:12},pairs:[{p_key:7,p_value:66}]}})
    B: debug.send(0,{mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})

We can see that the shard sent contains the key/value pair (7,66). Let's get the value remotely from process 0:

    A: debug.send(1,{mty:request_t,src:0,rq:{src:0,rkey:7,rtype:0,rdata:0,rtxid:0},num:2,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: true
    A: > debug.recv({mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:2,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.recv({mty:reply_t,src:1,rq:{src:0,rkey:7,rtype:0,rdata:66,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    A: debug.send(1,{mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
proto.answer(7,66,0)

    B: debug.recv({mty:request_t,src:0,rq:{src:0,rkey:7,rtype:0,rdata:0,rtxid:0},num:2,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: debug.send(0,{mty:ack_t,src:1,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:2,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: debug.send(0,{mty:reply_t,src:1,rq:{src:0,rkey:7,rtype:0,rdata:66,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})
    B: debug.recv({mty:ack_t,src:0,rq:{src:0,rkey:0,rtype:0,rdata:0,rtxid:0},num:1,sh:{lo:{is_end:0,val:0},hi:{is_end:0,val:0},pairs:[]}})

As expected, the request gets forward from process 0 to process
1. Notice also that we can see the sequence number incrementing in
successive packets.

Even after formal verification, there is still value
in testing. For example, we may have performance problems, or there
may be important properties that we didn't specify. In this case, we
were able to observe by testing that delegation is actually occurring,
which is not formally specified. In addition, we haven't proved any
progress properties. For all we know, our protocol can get into a
deadlock situation and stop responding. In the next section, we
discuss how to test more rigorously than we just did, to gain more confidence in our protocol implementation.



