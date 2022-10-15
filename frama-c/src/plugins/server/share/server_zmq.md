# ZeroMQ Protocol

This section presents a [ZeroMQ](http://zeromq.org) based entry point for Frama-C Server.
It is activated by option `-server-zmq <URL>` option of the Server plug-in, which is compiled
when the OCaml package `zmq` is detected at Frama-C configure time.

The protocol builds a ZeroMQ socket of type `REP` which is the standard for a request server.
It is meant for accepting connection from a ZeroMQ socket of type `REQ` on the same `URL`.
The paired `REP`-`REQ` sockets use
[ZeroMQ multi-part messages](http://zguide.zeromq.org/page:all#Multipart-Messages) to transfer data.

A typical example to start a Frama-C server for inter-process communication is:

```shell
$ frama-c [options...] -then -server-zmq ipc:///tmp/my-server.io
```

## Input Message Format

Each input message consists of a list of commands. Each command takes
a fixed number of parts from the incomming ZeroMQ message. The first part
of each command is a single string identifying the command:

| Commands | Parts | Part 1 | Part 2 | Part 3 | Part 4 |
|:--------|:-----:|:-------|:-------|:-------|:-------|
| `POLL()` | 1    | `"POLL"` | | | |
| `GET(id,request,data)`  | 4 | `"GET"` | id | request | data |
| `SET(id,request,data)`  | 4 | `"SET"` | id | request | data |
| `EXEC(id,request,data)` | 4 | `"EXEC"` | id | request | data |
| `SIGON(id)`  | 2 | `"SIGON"`  | id | | |
| `SIGOFF(id)` | 2 | `"SIGOFF"` | id | | |
| `KILL(id)`   | 2 | `"KILL"`   | id | | |
| `SHUTDOWN`   | 1 | `"SHUTDOWN"` | | | |

## Output Message Format

Each output message consists of a list of replies. Each reply takes
a fixed number of parts from the incomming ZeroMQ message. The first part
of each reply is a finel string identifying the reply:

| Replies | Parts | Part 1 | Part 2 | Part 3 |
|:--------|:-----:|:-------|:-------|:-------|
| `DATA(id,data)` | 3    | `"DATA"` | id | data |
| `ERROR(id,message)` | 4 | `"ERROR"` | id | message |
| `KILLED(id)` | 2 | `"KILLED"` | id | |
| `REJECTED(id)` | 2 | `"REJECTED"` | id | |
| `SIGNAL(id)`   | 2 | `"SIGNAL"` | id | |
| `CMDLINEON` | 1 | `"CMDLINEON"` | | |
| `CMDLINEOFF` | 1 | `"CMDLINEOFF"` | | |
| (special) | 2 | `"WRONG"` | message | |
| (special) | 1 | `"NONE"` | | |

The two special responses `"WRONG"` and `"NONE"` are used to handle special issues
with the ZeroMQ layer protocol: `WRONG(message)` signals an error in the message formats;
`NONE` is used in the special case where the reply message from the server is completely
empty. This generaly means that the server is busy or idled.

## Data Format

Request identifiers can be any string, encoded into a single part of a ZeroMQ message.

Data are stringified JSON data structures. Each command or reply data shall be packed
into a single JSON data, which leads to a single part of the associated ZeroMQ message.

Since ZeroMQ prococol accepts any kind of strings as a single
message part, the stringified JSON data might contains spaces, newlines and any
other spacing characters.
