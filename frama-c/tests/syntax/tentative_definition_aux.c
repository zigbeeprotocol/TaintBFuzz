/* run.config*
DONTRUN: primary test in tentative_definition.c
*/

#ifdef EEDN
#define LINKAGE_2 extern
#define DEF_2
#endif

// OK (one global, 0-initialized)
#ifdef EENN
#define LINKAGE_2 extern
#define DEF_2
#endif

// OK (one global, initialized to 2)
#ifdef ENND
#define LINKAGE_2
#define DEF_2 = 2
#endif

// OK (one global, 0-initialized)
#ifdef ENNN
#define LINKAGE_2
#define DEF_2
#endif

// OK-ish (two defs to 0)
#ifdef NNNN
#define LINKAGE_2
#define DEF_2
#endif

// KO (two conflicting defs)
#ifdef EEDD
#define LINKAGE_2 extern
#define DEF_2 = 2
#endif

// KO (two conflicting defs)
#ifdef ENDD
#define LINKAGE_2
#define DEF_2 = 2
#endif

// KO (two conflicting defs)
#ifdef ENDN
#define LINKAGE_2
#define DEF_2
#endif

// KO (two conflicting defs)
#ifdef NNDD
#define LINKAGE_2
#define DEF_2 = 2
#endif

// KO (two conflicting defs)
#ifdef NNDN
#define LINKAGE_2
#define DEF_2
#endif

LINKAGE_2 int x DEF_2;
