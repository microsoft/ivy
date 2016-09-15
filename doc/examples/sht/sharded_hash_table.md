---
layout: page
title: Introduction
---

In this section, we'll put together some of the previously developed
concepts into a more substantial service: a *sharded hash table*. This
is a directory service that is provided by a collection of
servers. The basic function is to get or set the value of a key in the
directory. The storage of key/values pairs, however, is distributed in
a way that a range of keys can be migrated dynamically from one server
to another in order to balance the load. A subset of the directory
will be called a *shard*.  Each server keeps a *delegation map* that
represents its notion of where the value of each key is actually
stored. If a server receives a request for a key that is not stored
locally, it uses the delegation map to determine where to forward the
request. Since the delegation maps can be out of date, a request might
have to be forwarded more than once in order to be served.

An important issue we will have to deal with in this example is
*concurrency semantics*. That is, our directory service can handle
many requests concurrently. We need to say what it means for
transactions that execute concurrently to be correct. The correctness
condition we will use is called
[linearizability](https://en.wikipedia.org/wiki/Linearizability).
We'll see how to specify linearizability and how to prove it in a
modular way.

Our system consists of the following objects, each of which provides a
service specification and an implementation:

- The [directory](proto.html) (a parameterized protocol)
- A [reference object](reference.html) that checks linearizability
- An abstract datatype for the [hash table](table.html)
- An abstract datatype for the [delegation map](delmap.html)
- A concrete datatype for [shards](shard.html)
- An ordered, non-duplicating network [transport protocol](trans.html)
- Abstract datatypes for [keys, values](key.html) and [sequence numbers](seqnum.html)

These modularly verified objects are assembled to produce the [sharded
hash table system](sht.html), which we can then compile and execute.






