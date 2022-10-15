Contributing to Frama-C
=======================

We always welcome technical as well as non-technical contributions from the
community.
There are several ways to participate in the Frama-C project:

- Asking questions and discussing at
  [StackOverflow](https://stackoverflow.com/tags/frama-c) and through
  the
  [Frama-C-discuss mailing list](https://lists.gforge.inria.fr/mailman/listinfo/frama-c-discuss);

- Reporting bugs via
  [Gitlab issues](https://git.frama-c.com/pub/frama-c/issues);

- [Submitting bug fixes, improvements and features](#submitting-bug-fixes-improvements-and-features)
  via Gitlab merge requests;

- [Developing external plug-ins](#developing-external-plug-ins)
  and sharing it with us through a Gitlab merge request;

- Joining the [Frama-C team](http://frama-c.com/about.html) (as an intern, a PhD
  student, a postdoctoral researcher, or a research engineer).

We give below some guidelines in order to ease the submission of a merge request
and optimize its integration with the Frama-C existing codebase.


Submitting bug fixes, improvements, and features
================================================

External contributions can be proposed via the
public Frama-C gitlab [repository](https://git.frama-c.com/pub/frama-c),
by following the recommended workflow in git development:
fork the frama-c repository, develop in a dedicated branch
and submit a merge request.

The detailed steps to submit a contribution to Frama-C are:

1. If you plan to make a significant contribution to Frama-C, please
  [open an issue](https://git.frama-c.com/pub/frama-c/issues/new)
  describing your ideas, to discuss it with the Frama-C development team.

2. [Fork the public Frama-C repository](https://git.frama-c.com/pub/frama-c/-/forks/new)
  (choosing your Gitlab account as a destination);

3. Clone the forked Frama-C snapshot repository on your computer;

4. Create and switch to a dedicated branch. We suggest the following
   naming convention:
   - `fix/short-description` for bug fixes (correcting an incorrect
     behavior);
   - `feature/short-description` for features (adding a new behavior).

5. Locally make your contribution by adding/editing/deleting files and following
  the [coding conventions](#coding-conventions);

6. (Optional) Locally add non-regression test cases to the appropriate
  subdirectory in `./tests/`. The `hello` tutorial in the
  [plug-in developer manual](http://frama-c.com/download/frama-c-plugin-development-guide.pdf)
  provides an example of the use of the dedicated `ptests`
  tool used by Frama-C developers. The full documentation for `ptests` is also
  present later in the same manual.
  You can also provide the non-regression test case in the Gitlab issue
  discussion and we will integrate it.

7. Check for unexpected changes.
  Use the command `make lint`
  in your terminal from the Frama-C root directory to detect trailing spaces,
  tabulations or incorrect indentation (ocp-ident >= 1.7.0 is needed).

8. Locally run the test framework of Frama-C by typing
  `make tests`
  in your terminal (you should be in the Frama-C root directory);

9. Locally add (if needed) and commit your contribution;

10. Push your contribution to Gitlab;

11. [Make a Gitlab merge request](https://git.frama-c.com/pub/frama-c/merge_requests).
  The target should remain as repository `pub/frama-c` and branch `master`
  while the source should be your personal project and your chosen branch
  name.

12. If needed (i.e. you didn't already do that and your contribution is
    not trivial in the sense of [this document](TCA.md)), please don't forget
    to fill and sign the [Contributor Licence Agreement](CLA.pdf) and send us
    the signed version at `cla AT frama-c DOT com`

For convenience, we recall the typical `git` commands to be used through these steps:
```shell
git clone https://git.frama-c.com/<username>/frama-c.git
git checkout -b <branch-name>
git diff --check
git add <file1 file 2>
git commit -m "<Commit message>"
git push origin <branch-name>
```
where:

- `<username>` is your Gitlab username;
- `<branch-name>` is your chosen branch name;
- `<file1 file2>` are the files to add to the commit;
- `<Commit message>` is your commit message.


Developing external plug-ins
============================

Frama-C is a modular platform for which it is possible to develop external
plug-ins as documented in the
[Plug-In development guide](http://frama-c.com/download/frama-c-plugin-development-guide.pdf).
Such plug-ins normally do not require changes to the Frama-C source code and can
be developed completely independently, for instance in a separate Git
repository as exemplified by the [Hello plug-in](https://github.com/Frama-C/frama-c-hello).

However, to make it easier for your users to compile and use your plug-in, even
as newer releases are made available, we recommend the following workflow:

1. Write your external plug-in as indicated in the
  [Plug-In development guide](http://frama-c.com/download/frama-c-plugin-development-guide.pdf);

2. Create an `opam` package by
  [pinning your local plug-in](http://opam.ocaml.org/doc/Packaging.html#Opam-pin) and
  [editing the `opam` file](http://opam.ocaml.org/doc/Packaging.html#The-quot-opam-quot-file).
  You can have a look at the
  [`opam` file of the Hello plug-in](https://github.com/Frama-C/frama-c-hello/blob/master/opam)
  if necessary.

3. Optionally
  [publish your plug-in](http://opam.ocaml.org/doc/Packaging.html#Publishing)
  in the official OPAM packages repository.

4. Announce your contribution to the Frama-C ecosystem on the
  [Frama-C-discuss mailing list](https://lists.gforge.inria.fr/mailman/listinfo/frama-c-discuss).
  Well done!

The main advantage of this procedure is that opam will perform several
consistency checks of your plug-in,
with respect to several Frama-C versions and OCaml dependencies.

Coding conventions
==================

- Use [ocp-indent](https://github.com/OCamlPro/ocp-indent), v1.8.1
  to indent OCaml source files;

- Avoid trailing whitespaces;

- Avoid using tabs;

- Strive to keep within 80 characters per line.
