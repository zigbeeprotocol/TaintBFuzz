/* run.config*
OPT: -cpp-extra-args="-DEEDN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DEENN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DENND" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DENNN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DNNNN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
EXIT: 1
OPT: -cpp-extra-args="-DEEDD" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DENDD" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DENDN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DNNDD" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
OPT: -cpp-extra-args="-DNNDN" %{dep:@PTEST_DIR@/@PTEST_NAME@_aux.c} -print
*/

// OK (one global defined to 1)
#ifdef EEDN
#define LINKAGE_1 extern
#define DEF_1 = 1
#endif

// OK (one global, 0-initialized)
#ifdef EENN
#define LINKAGE_1 extern
#define DEF_1
#endif

// OK (one global, initialized to 2)
#ifdef ENND
#define LINKAGE_1 extern
#define DEF_1
#endif

// OK (one global, 0-initialized)
#ifdef ENNN
#define LINKAGE_1 extern
#define DEF_1
#endif

// OK-ish (two defs to 0)
#ifdef NNNN
#define LINKAGE_1
#define DEF_1
#endif

// KO (two conflicting defs)
#ifdef EEDD
#define LINKAGE_1 extern
#define DEF_1 = 1
#endif

// KO (two conflicting defs)
#ifdef ENDD
#define LINKAGE_1 extern
#define DEF_1 = 1
#endif

// KO (two conflicting defs)
#ifdef ENDN
#define LINKAGE_1 extern
#define DEF_1 = 1
#endif

// KO (two conflicting defs)
#ifdef NNDD
#define LINKAGE_1
#define DEF_1 = 1
#endif

// KO (two conflicting defs)
#ifdef NNDN
#define LINKAGE_1
#define DEF_1 = 1
#endif

LINKAGE_1 int x DEF_1;

int main() { return x; }
