/* run.config
DONTRUN: bug fix in progress
MACRO: OUT @PTEST_NAME@_res.i
EXECNOW: LOG @OUT@ @frama-c@ @PTEST_FILE@ -ocode @PTEST_RESULT@/@OUT@ -print -then @PTEST_RESULT@/@OUT@ -print
 */
/* Generated by Frama-C */
/* Generated by Frama-C */
struct rr;
typedef struct rr rr;
struct apf;
struct rr {
   struct apf *of ;
};
typedef struct apf apf;
struct apf {
   apf *next ;
   rr *r ;
};
/*@ requires r->of == ((void *)0); */
static apf *f(rr *r)
{
  apf *__retres;
  __retres = r->of;
  return __retres;
}
