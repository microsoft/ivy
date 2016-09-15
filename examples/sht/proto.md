---
layout: page
title: Protocol
---

Now we get to the [actual protocol](proto.ivy). Each host has a hash
table and a delegation map describing where to find ranges of
keys. When the host receives a request to get or set the value of a
key in the directory, it looks up the key in the delegation map. If
the key is delegated to the local host, the operation is performed
directly on the host's hash table.  Otherwise, the request is
forwarded to the host indicated in the delegation map. Since the
delegation map of the local host may be out of date, the forwarded
request may be forwarded repeatedly until it reaches the host with
actual responsibility for the key. When this host receives the
forwarded request, it performs the operation on its local hash table
and returns a reply directly to the original requesting host. This
host then responds to the client with an answer.

Initially, all keys belong to the master server numbered `0`. A host
that serves a range of keys can delegate that range to another host by
extracting a shard and sending it in a *delegate* message. The host
receiving the delegate message incorporates the shard into its own
hash table.  Both hosts update their delegation maps
accordingly. Hosts don't make any attempt to advertise the keys that
they own to other hosts. This means that a request for a key must
follow the original chain of delegation to get to the owner of the
key.

# Specification

Here is the client-facing interface of the protocol:

    module sht_protocol(me,ref,trans,id,key,data,shard) = {

        action set(k:key.t,d:data) returns(ok:bool, tx:ref.txid)
        action get(k:key.t) returns(ok:bool, tx:ref.txid)
        action answer(k:key.t,d:data,tx:ref.txid)
        action delegate_(dst:id, lo:key.iter.t, hi:key.iter.t)  returns(ok:bool)
        ...

The parameters are `me`, the host's id, `ref`, the [reference
object](reference.html), `trans` the [transport service](trans.html)
and data types `id`, `key`, `data` and `shard` (`data` is the type of
values in the directory).

Notice that `set` and `get` return a parameter of type `ref.txid`, or
transaction id. This is a ghost type defined by the reference object
that is used to define linearizability. Transaction id's don't
actually appear in the compiled implementation. When the protcol calls
back to `answer`, it provides a ghost transaction id that allows us to
*specify* the correct data.

Here is the specification of this interface:

        object spec = {
            before set {
                tx := ref.begin(me,ref.write,k,d)
            }
            before get {
                tx := ref.begin(me,ref.read,k,0)
            }
            before answer {
                assert ref.data_(tx) = d
                call ref.end(tx)
            }
            before delegate_ {
                assert dst ~= me;
                assert lo < hi;
                assert key.iter.between(lo,K,hi) -> impl.dm.map(K,me)
            }
        }

The reference object is used to provide the specification of the
interface actions. In particular, calls to `set` and `get` begin new
transactions. The reference object's action `ref.begin` creates a new
transaction and provides the transaction id. Notice that the
transaction id is actually assigned in the specification
monitor. Normally specification monitors only make assertions about return
values. The actual return values are provided by the
implementation. However in the case of ghost values it is normal for
the specification itself to provide them.

The call-back `answer` ends the transaction and asserts that the data
it provides is correct for that transaction according to the reference
object. Notice that this is a *before* specification because `answer`
is a call-back. We expect the protocol to guarantee this assertion
before calling `answer`. If this is true, then we know that there
exists a linearization of the transactions that is consistent with the
answers we provide.

The specification of `delegate_` is interesting because it has no
post-condition.  This is because `delegate_` actually has no visible
effect to the user of the interface (other than, hopefully, on
performance). The pre-condition says we cannot delegate to ourselves,
we have to delegate at least one key and we must own all the keys that
are delegated. There is a slight violation of abstraction here, since
we refer to the abstract state of the delegation map, which is
internal. It would be better form to make a copy of this map and
describe the way that `delegate_` updates it. This way users of the
interface wouldn't have to peek inside the implementation to prove the
pre-condition. For now, though, we'll be lazy and not do that, since
this pre-condition is just an environment assumption that we won't
actually prove.

# Implementation

The implementation is, of course, the interesting part. We start by defining
a concrete `struct` for requests that we can pass over the network:

    object req = {
        type t = struct {
            src : id,
            rkey : key.t,
            rtype : ref.otype,
            rdata : data,
            rtxid : ref.txid
        }
    }

The `src` field allows the reply to be routed back to the source. The
key, operation type and data describe the requested operation. The
transaction id is ghost and is used only for specification purposes.

The implementation of a host contains a [hash table](table.html) and a [delegation map](delmap.html):

    object impl = {

        instance hash : hash_table(key,data,shard)

        instance dm : delegation_map(key,id)
        ...

Here is the internal action that handles a request, either locally, or by forwarding it:

        action handle_request(rq:req.t) returns(ok:bool) = {
            local src:id, k:key.t, op:ref.otype, d:data, tx:ref.txid, ow:id {
                src := req.src(rq);
                k := req.rkey(rq);
                op := req.rtype(rq);
                d := req.rdata(rq);
                tx := req.rtxid(rq);
                ow := dm.get(k);
                if ow = me {
                    call ref.commit(tx);  # this is ghost!
                    if op = ref.read {
                        req.rdata(rq) := hash.get(k)
                    }
                    else {
                        call hash.set(k,d)
                    };
                    ok := trans.send_reply(me, src, rq)
                } else {
                    ok := trans.send_request(me, ow, rq)  # forward request
                }
            }
        }

We start by extracting the fields of the request. Then we call the
delegation map `dm` to see who (we think) owns the request key. If the
owner is `me` (the local host) we call `ref.commit` to indicate that
the transaction is being commited now. This is possible because the
transaction id is a ghost field of the request. In the compiled code,
the reference object will be abstracted away, so this call will do
nothing. Then we execute the request. If it's a read, we get data from
the hash table.  If a write, we set data. The we send the modified
request back to the original requester as a reply. On the other hand,
if the owner is not `me` we forward the request to the owner. In
either case, to send a protocol message, we call the `trans` service.

Now we use `handle_request` to implement `set` and `get`. Here is `set`:

        implement set {
            local rq:req.t {
                req.src(rq) := me;
                req.rkey(rq) := k;
                req.rtype(rq) := ref.write;
                req.rdata(rq) := d;
                req.rtxid(rq) := tx;       # ghost!
                ok := handle_request(rq)
            }
        }

It just builds a request and calls `handle_request`. Notice though,
that the transaction id generated by the specification monitor (which
runs before the implementation) is inserted in the request. The implementaiton of `get` is similar:

        implement get {
            local rq:req.t {
                req.src(rq) := me;
                req.rkey(rq) := k;
                req.rtype(rq) := ref.read;
                req.rtxid(rq) := tx;
                ok := handle_request(rq)
            }
        }

The `delegate_` action is quite simple:

        implement delegate_ {
            call dm.set(lo,hi,dst);
            ok := trans.send_delegate(me,dst,hash.extract_(lo,hi))
        }

We set the range of keys in the delegation map, extract a shard and
call the transport service to send the shard.

Now we have to handle the incoming messages by implementing the
call-back actions of the transport service.  Incoming forward request
are handled like this:

        implement trans.recv_request(rq:req.t) {
            local ok : bool {
                ok := handle_request(rq)
            }
        }

That is, we just call `handle_request`. We ignore the `ok` flag
returned by `handle_request`. This means that if we don't have
resources to handle the request, the request just gets dropped. A good
exercise would be to and a return parameter to `trans.recv_request` so
that in case the request can't be served immediately, the packet will
not be acknowledged and will then be retried. This won't happen with
the current implementation of `queue`, however, which doesn't put a
limit on the number of enqueued messages (in practice this means that
if the queue exceeds the available menory resources, the server
process will stop).

Here is how we handle incomping replies:

        implement trans.recv_reply(rq:req.t) {
            call answer(req.rkey(rq),req.rdata(rq),req.rtxid(rq))
        }

That is, we just call back to `answer` with the information in the
reply (including thre ghost transaction id).

Finally, we handle incoming delegation messages like this:

        implement trans.recv_delegate(s:shard.t) {
            call dm.set(shard.lo(s),shard.hi(s),me);
            call hash.incorporate(s)
        }

That is, we add key range of the shard to our delegation map,
indicating the local host as owner. Then we incorporate the shard into
our hash table.

That's it for the protocol.

# Invariants

A fair number of invariants are needed in the proof of the protocol to
cover the various kinds of protocol messages that can be in transit
and to make sure that the global protocol state is consistent.

The global protocol state invariants are:

        # If I own this key, then my hash table data matches the reference object
	conjecture impl.dm.map(K,me) -> hash.hash(K) = ref.map(K)

        # If I own this key, then no one else does
	conjecture impl.dm.map(K,me) & X ~= me -> ~proto(X).impl.dm.map(K,X)

The second invarient refers to `proto`, which is a collection of all
hosts. This will be defined when we [instantiate the protocol](sht.md). 

The invariants for delegation message in transit are:

        # If I own this key, then no delegated shard does
        conjecture proto.impl.dm(me).map(K,me)
            -> ~(trans.delegated(X,S) & key.iter.between(shard.lo(S),K,shard.hi(S)))

        # No two delegated shards have keys in common
        conjecture trans.delegated(X,S) & key.iter.between(shard.lo(S),K,shard.hi(S))
                   & trans.delegated(X1,S1) & key.iter.between(shard.lo(S1),K,shard.hi(S1))
                   -> X = X1 & S = S1

        # Delegated shards have correct data relative to reference object
        conjecture trans.delegated(X,S) & key.iter.between(shard.lo(S),K,shard.hi(S))
                    -> shard.value(S,K) = ref.map(K)

        # Every shard in transit is valid
        conjecture trans.delegated(D,S) -> shard.valid(S)

Notice we state that data in a shard in transit have to reflect all
commited transactions.  This key invariant holds because data in
transit is owned by no one and thus can't be modified.

For forwarded requests, we have:

        # Forwarded requests have correct operations relative to the reference object
        conjecture trans.requested(D,R) & L = req.rtxid(R)->
                   (req.rkey(R) = ref.key_(L) &
                    req.rtype(R) = ref.type_(L) &
                    (req.rtype(R) = ref.write -> req.rdata(R) = ref.data_(L)))

        # All forwarded requests have been generated but not committed
        conjecture trans.requested(D,R) -> ref.generated(req.rtxid(R)) & ~ref.committed(req.rtxid(R))

        # No two forwarded requests with the same txid
        conjecture trans.requested(D1,R1) & trans.requested(D2,R2) & req.rtxid(R1) = req.rtxid(R2)
                   -> D1 = D2 & R1 = R2

Notice how we use the reference object to specify correctness of data
in flight. This is possible because of the ghost transaction id's in
the messages.

For forwarded replies, we have similar invariants:

        # Forwarded replies have correct operations relative to the reference
        conjecture trans.replied(D,R) & L = req.rtxid(R)->
                   (req.rkey(R) = ref.key_(L) &
                    req.rtype(R) = ref.type_(L) &
                    req.rdata(R) = ref.data_(L))

        # All forwarded replies have been generated and committed
        conjecture trans.replied(D,R) -> ref.generated(req.rtxid(R)) & ref.committed(req.rtxid(R))

        # No two forwarded replies with the same txid
        conjecture trans.replied(D1,R1) & trans.replied(D2,R2) & req.rtxid(R1) = req.rtxid(R2)
                   -> D1 = D2 & R1 = R2

Notice that replies differ from requests in that they represent committed transactions.

These invariants are inductive and imply that the protocol satisfies
its service specification.  We'll prove that in the next section.

