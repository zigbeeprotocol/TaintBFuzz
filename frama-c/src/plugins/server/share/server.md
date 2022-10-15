# Architecture

The Server plug-in provides a _remote procedure call_ (RPC) interface to foreign
applications.  The protocol is organized in three logic layers, organized as
follows:

1. Many external entry points, based on various networking and system facilities
2. A generic logic run-time responsible for scheduling the requests coming from
   the various entry points
3. The Frama-C implementation of requests handler, at the kernel or plug-in
   level

The intermediate, logic layer, is responsible for adding a small bit of
parallelism upon the intrinsically synchronous behavior of Frama-C. This makes
Frama-C resembling an asynchronous RPC server.

The externally visible layer is only focused on transporting external requests
to the logic layer, and transporting back the results to the caller. The only
requirement for an entry point is to be able to transport a sequence of 1-input
message for 1-output message over time.

The concrete layer is implemented by the Frama-C kernel and its plug-ins. All
requests must be registered _via_ the Frama-C Server OCaml API in order to be
accessible from the entry-points. Some parts of this documentation are
automatically generated from the registered requests.

## Logical Requests

From a functional point of view, requests are remote procedures with input
data that reply with output data. Each request is identified by a unique name.
Input and output parameters are encoded into JSON values.

To adapt the internal synchronous Frama-C implementation with the external
asynchronous entry points, requests are classified into three kinds:

- `GET` to instantaneously return data from the internal state of Frama-C
- `SET` to instantaneously modifies the state or configure Frama-C plug-ins
- `EXEC` to starts a resource intensive analysis in Frama-C

During an `EXEC` requests, the implementation of the all resource demanding
computations shall repeatedly call the yielding routine `Db.yield()` of the
Frama-C kernel to ensures a smooth asynchronous behavior of the Server. During a
_yield_ call, the Server would be allowed to handle few `GET` pending requests,
since they shall be fast without any modification. When the server is idled, any
kind of requests can be started.

To summarize:

| Request | During Yields | Allowed to Yield | Computation  |
|:--------|:-------------:|:----------------:|:------------:|
| `GET`   | ✓ | - | fast, pure |
| `SET`   | - | - | fast, side-effects |
| `EXEC`  | - | ✓ | resource demanding |

## Server Signals

In response to a logical requests, the server might also emit _signals_
to the client. However, since a lot of signals might be emitted, the server
must be aware of which signals the client is listening to.
Signal are identified by unique strings.

The server and client can exchange other special commands to manage signals:

| Command | Issued by | Effect                      |
|:--------|:---------:|:----------------------------|
| `SIGON s` | client | start listening to signal `<s>` |
| `SIGOFF s` | client | stop listening to signal `<s>` |
| `SIGNAL s` | server | signal `<s>` has been emitted  |
| `CMDLINEON` | server | execution of the Frama-C command line |
| `CMDLINEOFF` | server | termination of the Frama-C command line |

When one or many requests emit some signal `<s>` several times,
the client would be notified only once per cycle of data exchange.
Signals will be notified in addition to responses or logical requests
or server polling.

During the execution of the Frama-C command line, the server behaves just like
during an `EXEC` request: only `GET` requests are processed at `Db.yield()` calls
until the (normal) termination of the command line.

## Transport Messages

From the entry points layer, the asynchronous behavior of the Server makes
output data and input data to be dispatched into different messages. However,
from the Client side, we still want to have _one_ response message for each
incoming message. However, answer messages might contains output data from
potentially _any_ previously received requests.

When the client has no more requests to send, but is simply waiting for pending
requests responses, it must periodically send _polling_ requests to simply get
back the expected responses.

To implement those features, the Client-Server protocol consists of a sequence of
paired _intput messages_ and _output messages_. Each single input message consists of
a list of _commands_:

| Commands | Parameters | Description |
|:---------|:-----------|:------------|
| `POLL` | - | Ask for pending responses and signals, if any |
| `GET` | `id,request,data` | En-queue the given GET request |
| `SET` | `id,request,data` | En-queue the given SET request |
| `EXEC` | `id,request,data` | En-queue the given EXEC request |
| `SIGON` | `id` | Start listening to the given signal |
| `SIGOFF` | `id` | Stop listening to the given signal |
| `KILL` | `id` | Cancel the given request or interrupt its execution |
| `SHUTDOWN` | - | Makes the server to stop running |

Similarly, a single output message consists of a list
of _replies_, listed in table below:

| Replies  | Parameters | Description |
|:---------|:-----------|:------------|
| `DATA` | `id,data` | Response data from the identified request |
| `ERROR` | `id,message` | Error message from the identified request |
| `SIGNAL` | `id` | The identified signal has been emitted since last exchange |
| `KILLED` | `id` | The identified request has been killed or interrupted |
| `REJECTED` | `id` | The identified request was not registered on the Server |
| `CMDLINEON` | - | The command line has started |
| `CMDLINEOFF` | - | The command line is terminated |

The logic layer makes no usage of _identifiers_ and simply pass them unchanged into
output messages in response to received requests.

At the transport message layer, input and output data are made of a
single `JSON` encoded value. Requests are identified by string, and
request identifiers can be of any type from the entry-points.

**Remark** the `GET`, `SET` or `EXEC` behavior of a request is actually defined
by the request implementation, from the Frama-C internal side. The Server will
silently ignore the request kind from the incoming messages and use the actual
internal one instead.  The distinction still appears in the transport protocol
only for a purpose of information, as clients shall know what they are asking
for.

## Entry Points

Implementations of entry points layers shall provide a non-blocking `fetch`
function that possibly returns a list of commands, associated with a
callback for emitting the paired list of replies. The Server main
loop is guaranteed to invoke the callback exactly once.

To integrate your own server into the Frama-C command-line framework, you need to
provide an implementation of the non-blocking `fetch` function and create a server
with `Server.create`. Then, you shall:

- Schedule `Server.start myServer` during the main plug-in extension phase _via_
  `Db.Main.extend`;

- Schedule `Server.run myServer` at normal command line termination phase _via_
  `Cmdline.at_normal_exit`;

- Schedule `Server.stop myServer` with other cleaning operations at exit phase
  _via_ `Extlib.at_exit_safe`.

This way, your server will integrate well with the command line execution of
Frama-C and the other plug-ins.

## Request Implementations

It is the responsibility of Frama-C plug-ins to implement and register requests
into the Server to make them accessible _via_ any entry point. Whereas data is
encoded into JSON structures at the transport layer, requests are processes with
well typed OCaml types from the internal side.

Hence, the requests implementations also requires data encoder and decoders to
be defined. Some predefined data types are provided by the Server plug-in, but
more complex types can be defined and shared among plug-ins _via_ the
`Server.Data` module factory.

Registration of requests, data encoder and decoders always comes with their
markdown documentation thanks to the `Markdown` library provided by the Frama-C
kernel. Hence, a full documentation of all implemented requests with their data
formats can be generated consistently at any time. See option `-server-doc` of the
Server plug-in for more details.
