---
layout: page
title: Message Queues
---

Our message transport service needs an abstract type of [message
queues](queue.ivy) to support reliable delivery. The message queue
holds messages that have been sent (to a particular host) but whose
delivery has not yet been acknowledged.

Here is the interface for message queues:

    module message_queue(net_msg,seq_num) = {

	action enqueue(msg:net_msg.t) returns (ok:bool)
	action empty returns (res:bool)
	action pick_one returns (res:net_msg.t)
	action delete_all(seq:seq_num)

	...

The module takes a type `net_msg` of messages and type `seq_num` of
sequences numbers as parameters. It assumes that `seq_num` has an
iterator type and that `net_msg` has a destructor `num` that yields
the sequence number of a message.

The `enqueue` action adds a message
to the queue, returning true if the action was successful. This allows
the implementation the flexibility to fail if there are insufficient
resources.  The `empty` action returns true if the queue is empty,
`pick_one` returns some message from a non-empty queue and
`delete_all` removes all of the messages with sequence number less
than or equal to `seq_num`.

The abstract state of the queue is held by the predicate `contents`
which represents the set of all messages currently in the queue:

    relation contents(M:net_msg.t)

Here is the specification of the interface:

	object spec = {
	    after init {
                contents(M) := false
            }

	    before enqueue {
		assert contents(X) -> net_msg.num(X) ~= net_msg.num(msg)
	    }

	    after enqueue {
		if ok {
		    contents(msg) := true
		}
	    }

	    after empty returns (res:bool) {
		call impl.spec.lemma;
		assert contents(M) -> ~res;
		assert ~res -> exists M. contents(M)
	    }

	    before pick_one {
		assert exists M. contents(M);
		call impl.spec.lemma
	    }

	    after pick_one {
		assert contents(res)
	    }

	    before delete_all  {
		contents(M) := contents(M) & ~(net_msg.num(M) <= seq)
	    }
	}
    
Nootice the the `contents` predicate is updated in the *after*
specification of `enqueue`. This is because the update depends on the
return value `ok`.  Also, we are not allow to enqueue a message with
the same sequence number as a message already in the queue, and
`pick_one` has the pre-condition that the queue is not empty.

We can implement this specification in a number of ways. Here is a
simple implementation that uses an ordered map from sequence numbers to
messages:

    object impl = {

	instance imap : ordered_map(seq_num,net_msg.t)

	implement enqueue {
	    call imap.set(net_msg.num(msg),msg);
	    ok := true
	}

	implement empty {
	    res := seq_num.iter.is_end(imap.lub(seq_num.iter.create(0)))
	}
	
	implement delete_all(seq:seq_num.t) {
	    call imap.erase(seq_num.iter.create(0),seq_num.iter.create(seq_num.next(seq)))
	}

	implement pick_one {
	    res := imap.get(seq_num.iter.val(imap.lub(seq_num.iter.create(0))))
	}

	conjecture imap.maps(X,Y) -> X = net_msg.num(Y)
	conjecture contents(Y) <-> imap.maps(net_msg.num(Y),Y)

    }

Since we do not bound the size of the queue, `enqueue` always returns
true. It just maps the message's sequence number to the mesage. The
`delete_all` implementation erases all the messages with numbers in
the range `[0,seq+1)`. The `pick_one` action actually returns the
message in the queue with the least serial number. This is a good
choice from the point of view of progress, since repeatedly sending
this message will be guaranteed to eventually produce an ack. We will
not, however, prove progress.

The two invariant conjectures show are enough to prove the
implementation. The first says that sequence number `X` always maps to
a message with number `X`.  The second is essentially the
representation function. It says that the contents of the queue is the
set of message such that are mapped to by their sequence number.


