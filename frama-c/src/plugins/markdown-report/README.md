Generation of pandoc and/or sarif reports.

# Dependencies

## Mandatory
- packages `ppx_deriving`, `ppx_deriving_yojson` and `yojson`

## Optional
- FlameGraph ([`https://github.com/brendangregg/FlameGraph`](https://github.com/brendangregg/FlameGraph))

# Usage

`markdown-report` focuses on results computed by Eva and WP.
It has three output formats, controlled by the `-mdr-gen` option:

- `draft`: produces a markdown report with placeholders for writing (markdown)
comments on the various items (e.g. why is an alarm spurious, or why is
a given hypothesis safe).
- `markdown`: produces a full-fledged markdown report. It can be used in
  conjunction with the option `-mdr-remarks <f>` which will use the
  remarks written in the draft document `f` (which is supposed to have been
  generated from the same analysis in `draft` mode and edited with manual
  comments afterwards).
- `sarif`: produces a json object in the Static Analysis Results Interchange
  Format (SARIF), as documented [here](https://github.com/oasis-tcs/sarif-spec).
  This output is very experimental and lacks many information contained in
  the `markdown` format. It can also incorporate remarks from `-mdr-remarks`,
  that will be reflected as `message`s in the `sarif` object.

The output file can be controlled with `-mdr-out`. Other options are:

- `-mdr-authors`: comma separated list of the authors of the document
- `-mdr-title`: give a title to the document
- `-mdr-flamegraph`: generate a flamegraph in the given file (see below)
- `-mdr-stubs`: identifies a set of files as containing stubs for Eva (i.e.
  code that is not in the scope of the analysis per se).

Sarif document can be validated against the spec
[online](https://sarifweb.azurewebsites.net/Validation)

## Flamegraph
Checking out [`https://github.com/Frama-C/open-source-case-studies`](https://github.com/Frama-C/open-source-case-studies), start with a simple analysis and generate the intermediary SVG and Markdown files.

```shell
frama-c -eva 2048.c -eva-flamegraph="flamegraph.txt" -save snap.sav
flamegraph.pl ./flamegraph.txt > flamegraph.svg
frama-c -load snap.sav -mdr-gen -mdr-flamegraph="./flamegraph.svg"
```

Then generate a report in your favorite open format (requires the
[pandoc](http://pandoc.org/) document generator

```shell
pandoc -o report.docx report.md
```
