/* run.config
   PLUGIN: wp
   OPT: -region-annot -print
   EXECNOW: BIN ocode_@PTEST_NAME@_1.i @frama-c@ %{dep:@PTEST_DIR@/@PTEST_NAME@.i}            -region-annot -print -ocode @PTEST_RESULT@/ocode_@PTEST_NAME@_1.i > @DEV_NULL@ 2> @DEV_NULL@
   EXECNOW: BIN ocode_@PTEST_NAME@_2.i @frama-c@ %{dep:@PTEST_RESULT@/ocode_@PTEST_NAME@_1.i} -region-annot -print -ocode @PTEST_RESULT@/ocode_@PTEST_NAME@_2.i > @DEV_NULL@ 2> @DEV_NULL@
   EXECNOW: LOG  diff_@PTEST_NAME@.txt diff %{dep:@PTEST_RESULT@/ocode_@PTEST_NAME@_1.i} %{dep:@PTEST_RESULT@/ocode_@PTEST_NAME@_2.i} &> @PTEST_RESULT@/diff_@PTEST_NAME@.txt
COMMENT: The file diff_@PTEST_NAME@.txt must be empty.
COMMENT: So, that file has not to be present into the oracle directory since absent files are considered such as empty files.
 */

/* run.config_qualif
   DONTRUN:
*/

// This test only checks that annotation are correctly parsed & printed

typedef struct N { double v ; int s ; } *SN ;
typedef struct L { int v ; int s ; } *SL ;

typedef struct Block {
  SN prm ;
  SN inp1 ;
  SN inp2 ;
  SN inp3 ;
  SN out1 ;
  SN out2 ;
  SN out3 ;
  SL idx1 ;
  SL idx2 ;
  SL idx3 ;
  SN sum ;
} FB ;

//@ region *fb ;
void fb_ADD(FB *fb)
{
  fb->out1->v = fb->out1->v + fb->out2->v ;
  fb->out1->s = fb->out1->s | fb->out2->s ;
}

/*@
  region IN:   (fb->inp1 .. fb->inp3), \pattern{PMEM} ;
  region OUT:  (fb->out1 .. fb->out3), \pattern{PVECTOR} ;
  region IDX:  (fb->idx1 .. fb->idx3), \pattern{PVECTOR} ;
 */
void fb_SORT(FB *fb)
{
  SN *inp = &(fb->inp1) ;
  SN *out = &(fb->out1) ;
  SL *idx = &(fb->idx1) ;

  for (int i = 0; i < 3; i++) {
    out[i]->v = inp[i]->v + fb->prm->v ;
    out[i]->s = 0 ;
    idx[i]->v = inp[i]->s ;
    idx[i]->s = 0 ;
  }

  fb->sum->v =
    fb->out1->v +
    fb->out2->v +
    fb->out3->v ;

  fb->sum->s = 0 ;

}
