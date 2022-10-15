The following set of packages is known to be a working configuration for
compiling Frama-C+dev, on a machine with gcc <= 9[^gcc-10]

NB: frama-c-gui can be compiled against either lablgtk3 or lablgtk2. However, gtk2 itself
is deprecated on most distributions, and it can be difficult to install the appropriate
support libraries (notably gtksourceview). lablgtk3 should be preferred.

- OCaml 4.08.1
- alt-ergo.2.2.0 (for wp, optional)
- apron.v0.9.13 (for eva, optional)
- coq.8.13.0 (for wp, optional)
- lablgtk3.3.1.1 + lablgtk3-sourceview3.3.1.1 | lablgtk.2.18.11
- mlgmpidl.1.2.14 (for eva, optional)
- ocamlfind.1.8.1
- ocamlgraph.1.8.8
- ppx_deriving_yojson.3.6.1 (for mdr, optional)
- ppx_import.1.9.1
- why3.1.5.0
- yojson.1.7.0
- zarith.1.12

[^gcc-10]: As mentioned in this [OCaml PR](https://github.com/ocaml/ocaml/issues/9144)
gcc 10 changed its default linking conventions to make them more stringent,
resulting in various linking issues. In particular, only OCaml >= 4.10 can be
linked against gcc-10.
