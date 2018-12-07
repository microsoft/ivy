---
layout: page
title: Reference object
---

In this section, we'll introduce the notion of linearizability as our
concurrency semantics, and see how to define a monitor for
linearizability. We'll call this monitor the *reference object*.

Our service specification has requests and responses. We'll refer to a
request/response pair as a *transaction*. Suppose that transactions
occur sequentially (that is, no transaction starts until the previous
transaciton is completed).  In this case it's easy to say what a
correct response is.  Each `set` transaction results in mutating the
value of one key in the abstract directory. Each response transaction
yields the current value of the given key. These properties define a
*consistent* sequential execution.

But what about the case when transactions can occur concurrently?  In
what order should changes to the directory occur? Which values should
be returned?

Linearizability gives one possible way to answer these questions.  It
says that a *concurrent* execution is consistent if there exists a
corresponding *sequential* execution such that each sequential
trancation occurs within the time bounds of the corresponding
concurrent transaction. In other words, although a transaction takes
time, it appears as if it occurs at a single point in time.

Let's try to make this idea a little more mathematically precise. We
have a set of transactions that have corresponding requests and
responses. The transactions are partially ordered by a relation we
call "happens before". We as `t1` happens before `t2` if the response
of `t1` occurs temporally before the request of `t2`.

An execution is linearizable if there exists a total order `<` on the
transactions such that:

- if `t1` happens before `t2` then `t1 < t2`, and
- the transactions ordered by `<` are consistent.

Consistency means that the value returned by a `get` transaction `t` for
key `k` is the value of the most recent `set`
transaction to `k` according to `<`.

Linearizability is easy to describe on paper, but not so easy to
specify in IVy.  This is because there is no way to state in IVY's
first-order logic that there *exists* a relation `<` having some
property. Instead, we will provide an object that *constructs* the
order `<` by monitoring the behavior of the protocol. This is the
reference object.

The state of the reference object has several components:

- A set of transactions
- The "happens before" relation on transactions
- A subset of *committed* transactions
- An abstract directory state

The reference object monitors requests and responses, accumulating the
set of transactions, and keeping track of the "happens before"
relation. It also provides a "ghost" action called `commit`. When
`commit` is called, the given transaction is executed on the abstract
state and added to the committed set. The precondition to `commit`
transaction `t` is that every transaction that happens before `t` is
already committed. In this case, the order of committing transactions
is a consistent sequential order `<` (and IVy can prove this).

The `commit` action is special because we don't actually indend to
execute it in reality. When we extract code to execute, the `commit`
actions will be abstracted away. This lets us decorate our code with
`commit` actions to help in the proof.

The reference object's specification starts like this:

    module sht_reference(id,key,data) = {

        type otype = {read, write}

        ghost type txid

        function type_(T:txid) : otype
        function key_(T:txid) : key.t
        function data_(T:txid)  : data


We have an emumerated `otype` to represent the operation type, and an
uninterpreted ghost type `txid` to represent transactions. Because
`txid` is a ghost type, values of this type can't occur in extracted
code. We'll see how ghost types are used shortly.  The functions
`type_`, `key_` and `data_` tell us respectively the operation type, key
and data value associate with the transaction.

This is the monitor state:

        relation generated(T:txid)
        after init {
            generated(T) := false
        }

        relation committed(T:txid)
        after init {
            committed(T) := false
        }

        individual map(A:key.t) : data
        after init {
            map(A) := 0
        }

We keep track of a set of `generated` transactions (those that have
begun) as well as a set of `committed` transactions, and the abstract state
`map` of the directory.  Initially, all keys map to value `0`.

The `begin` action is called when a transaction starts. It allocates a
fresh transaction id, builds a transaction with that id and adds the
transaction to the set `generated`. Being lazy, we assume that there
is always an unused transaction id available. We could prove this by
implementing `txid` with, for example, the integers.

        action begin(i:id, o:otype, k:key.t, d:data) returns (lt:txid) = {
            assume exists T. ~generated(T);
            if some c:txid. ~generated(c) {
                type_(c) := o;
                key_(c) := k;
                data_(c) := d;
                generated(c) := true;
                lt := c
            }
        }

Notice that the `begin` action returns a transaction id. This ghost
value can be used by the protocol implementation to indicate when a
transaction is being committed.

The commit action is called by the protocol to do just that. Here is its
specification:

        action commit(lt:txid)

        before commit {

            assert generated(lt) & ~committed(lt);
            committed(lt) := true;

            if type_(lt) = read {
                data_(lt) := map(key_(lt))
            }
            else {
                map(key_(lt)) := data_(lt)
            }                        
        }     

The precondition for this operation is that the operation has begun,
but has not yet committed. We add the `txid` to the commited set and
execute the transaction abstractly. If it is a `read`, we set the
transaction's data based on the current abstract state. If a write, we
set the abstract state based on the transaction's data.

Finally, when a transaction ends, we have to verify that it has
committed (that is, every transaction must commit between begin and
end).

        action end(lt:txid)
        before end {
            assert commited(lt)
        }        
    }

In principle, we can now write a monitor for the reference object that
maintains the "happens before" relation and checks that the actual
commit order is consistent with "happens before". We'll leave that
problem for later however, and just trust that our reference object is
correct. The reference object is all we really need, since it can be
used as a specification of our protocol by a client in order to prove
the client correct.



