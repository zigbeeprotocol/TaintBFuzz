This directory contains the kernel backend.

It is low-level files which are internally used by other parts of the kernel, in
particular to build the AST from the annotated C input files into an AST.

It should not contain any useful APIs for the plug-in developers, except for
very low-level interactions and corner cases.
