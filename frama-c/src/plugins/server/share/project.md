# Project Management

The Frama-C current project can be managed with the server requests provided below.

## Current Project

Initially, the current project is the one selected when the server starts.
Hence, from the Frama-C command line, `-then-on <P> -server-xxx`
would start the server with current project `<P>`.

When modifying the current project through request `Kernel.Project.SetCurrent`,
client shall wait for an acknowledgement before sending further `GET` requests.
Otherwise, the `GET` might be executed on a different project, due to the
asynchronous behavior of the server.

However, it is still possible to execute a request on a specific project with
`Kernel.Project.{Get|Set|Exec}On` requests.
