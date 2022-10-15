# Ast Services

The Frama-C internal representation of source files need to be computed before
being accessed.  This generally involves preprocessing of sources and finally
parsing, typechecking and normalization.

Although this step is generally performed silently on-demand inside Frama-C,
from the Server point of view, this is a non-trivial procedure that should _not_ be
triggered outside an `EXEC` request.

Hence, most AST services might fail or return empty data if the AST has not been
actually computed before. However, in typical usage of Frama-C from the
command-line, the AST would have been computed just before any other plug-in,
including the Server.
