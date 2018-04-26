
```
include order
include collections
include byte_stream

```
TLS Records
===========

This document describes the structure of records transferred by the TLS version 1.2. Currently,
this is not a fully general description. In particular, it does not allow for TLS messages that
span multiple TLS records.



```
object tls = {

```
### Protocol version

Protocol verion is two bytes, encoded as follows:

| hi byte | lo byte | TLS version |
|---------|---------|-------------|
| 3       | 3       | 1.2         |

```
    type protocol_version
    interpret protocol_version -> bv[16]

```
### Records

A record encapsulates TLS messages. Its fields are:

- `ctype` a one-byte content type descriptor, encoded as follows:

    | ctype | content type       |
    |-------|--------------------|
    | 20    | change cipher spec |
    | 21    | alert              |
    | 22    | handshake          |
    | 23    | application data   |

- `version` the protocol version

- `fragment` the record content

In general, messages may span fragment boundaries, but we do not
allow that here. The content type field indicates the type of messages
occurring in the fragment, as detailed below. 

```
    type record = struct {
        ctype : byte,
        version : protocol_version,
        fragment : stream_data
    }

```
### Content types

This section details the various content types that may appear
in serialized form in a record.

#### Handshake

The handshake protocol uses messages of type `handshake`. 


```
    type handshake

```
A handshake message has the following variants:

| variant      | description  | tag |
|--------------|--------------|-----|
| client_hello | Client Hello | 1   |

The serialized form of `handshake` has the following four-byte prefix:

| byte 0 | bytes 1..3 |
|--------|------------|
| tag    | length     | 

where "length" is the length of the subsequent message in bytes.


##### Extensions

A sequence of extension fields may be appended to a handshake message.
An extension has the following fields:

- `etype` The extension type, encoded in two bytes
- `content` The extension content as a byte stream. In serialized form,
  this is prefixed by a two-byte length field.

```
    type extension
```
   instance extension_idx : unbounded_sequence
   instance extension_seq : array(extension_idx,extension)

##### Client Hello

The time in milliseconds since Jan 1, 1970 GMT is encoded as a 32-bit field.

```
    type gmt
    interpret gmt -> bv[32]

```
Random information is encoded in the following form. The
`random_bytes` field consists of exactly 28 bytes.

```
    type random = struct {
        gmt_unix_time : gmt,
        random_bytes : stream_data
    }

```
A cipher suite descriptor is a two-byte field used to indicate
a combination of cryptographic algorithms.

```
    type cipher_suite 
    interpret cipher_suite -> bv[16]

```
A `cipher_suite_seq` is a sequence of cipher suite descriptors in
order of preference. In serialized form it is prefixed by a two-byte
length field.

```
    instance cipher_suite_idx : unbounded_sequence
    instance cipher_suite_seq : array(cipher_suite_idx,cipher_suite)

```
The Client Hello message has the following fields:

- `client_version` The protocol version in use by the client

- `rand_info` The random information

- `session_id`  a token that is transmitted by the client to refer
  to a previously established session. If there is no prior session, this
  field contains zero bytes. In serialized form it is prefixed by a one-byte
  length field.

- `cipher_suites` is a sequence of cipher suite descriptors

- `compression_methods` is a sequence of one-byte compression method descriptors.
  In serialized for it is prfixes by a one-byte length field.

```
    variant client_hello of handshake = struct {
        client_version : protocol_version,
        rand_info : random,
        session_id : stream_data,
        cipher_suites : cipher_suite_seq,
        extensions : vector[extension]
    }


}
