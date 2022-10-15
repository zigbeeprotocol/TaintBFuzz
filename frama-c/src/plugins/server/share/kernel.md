# Kernel Services

This section deals with requests related to the management
of the Frama-C platform and services offered by the kernel.
This covers several topics: configuration, logs.

Configuration deals with versioning and resource directories.
Project services allow to work with several Frama-C projects.

Logs are automatically tracked by the server plug-in and queued.
This monitoring can be controlled by `Kernel.SetLogs` command, but by
default, monitoring is turned on as soon as some server is started
(except for the batch server). The `Kernel.GetLogs` allow to flush this queue,
with a maximum number of messages. Non-flushed messages
can be recovered by subsequent calls, until the requests replies with an empty
message set.

However, logs emitted prior to the execution of a server, or after its shutdown,
are _not_ collected by default. To enable this monitoring, for instance to collect
messages before the server is started, you shall set the `-server-logs` option, which
takes effect at configuration time (you can also use `... -then -server-logs ...`).
