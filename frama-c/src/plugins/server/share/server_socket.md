# Unix Sockets Protocol

This section presents entry point for Frama-C Server based on standard Unix
Sockets.  It is activated by option `-server-socket <URL>` option of the Server
plug-in, which is compiled when the OCaml package `zmq` is detected at Frama-C
configure time.

The protocol builds a pair of Unix sockets from the OCaml unix standard library.

```shell
$ frama-c [options...] -then -server-socket /tmp/my-server.io
```

## Messages Chunk Format

Messages are exchanged through non-blocking I/O on sockets input and output streams.
Each individual message is formatted into _chunks_ with any of the following formats:

    | 'S' |  3-HEX | n-DATA | -- with n = 0xHHH
    | 'L' |  7-HEX | n-DATA | -- with n = 0xHHH,HHHH
    | 'W' | 15-HEX | n-DATA | -- with n = 0xHHH,HHHH,HHHH,HHHH

The first byte of a message chunk is one ASCII character encoding the data-length format:
- `'S'` (short) : the length consists of 3 hex-digits in ASCII format;
- `'L'` (long) : the length consists of 7 hex-digits in ASCII format;
- `'W'` (wide) : the length consists of 15 hex-digits in ASCII format.

The last part of the message consists of `0xHEX` bytes of data, which is an `UTF-8`
encoded JSON data.

## Input Message Format

An input message chunk consists of a single command encoded as follows:

| Commands | JSON Message |
|:--------|:--------------|
| `POLL` | `"POLL"` |
| `SHUTDOWN` | `"SHUTDOWN"` |
| `GET(id,request,data)`  | `{ cmd = 'GET', id, request, data }` |
| `SET(id,request,data)`  | `{ cmd = 'SET', id, request, data }` |
| `EXEC(id,request,data)` | `{ cmd = 'EXEC', id, request, data }` |
| `SIGON(id)`  | `{ cmd = 'SIGON', id }` |
| `SIGOFF(id)` | `{ cmd = 'SIGOFF', id }` |
| `KILL(id)`   | `{ cmd = 'KILL', id }` |

## Output Message Format

An output message chunk consists of a single response encoded as follows:

| Response | JSON Message |
|:--------|:--------------|
| `DATA(id,data)` | `{ res = 'DATA', id, data }` |
| `ERROR(id,msg)` | `{ res = 'ERROR', id, msg }` |
| `KILLED(id)` | `{ res = 'KILLED', id }` |
| `REJECTED(id)` | `{ res = 'REJECTED', id }` |
| `SIGNAL(id)`   | `{ res = 'SIGNAL', id }` |
| `CMDLINEON` | `"CMDLINEON"` |
| `CMDLINEOFF` | `"CMDLINEOFF"` |

The special last case is used when the server is busy or died or some low-level
error occurs.

## Data Format

Request identifiers can be any JSON string and data are in JSON format.
