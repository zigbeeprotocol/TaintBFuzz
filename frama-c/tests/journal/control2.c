/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
 PLUGIN: @EVA_PLUGINS@
   EXECNOW: BIN control_journal2.ml @frama-c@ -journal-enable -eva -deps -out -main f -journal-name @PTEST_RESULT@/control_journal2.ml @PTEST_FILE@ > @DEV_NULL@ 2> @DEV_NULL@
 SCRIPT: @PTEST_RESULT@/control_journal2.ml
   EXECNOW: LOG control2_sav.res LOG control2_sav.err BIN control_journal_next2.ml @frama-c@ -journal-enable -lib-entry -journal-name @PTEST_RESULT@/control_journal_next2.ml @PTEST_FILE@ > @PTEST_RESULT@/control2_sav.res 2> @PTEST_RESULT@/control2_sav.err
 SCRIPT: @PTEST_RESULT@/control_journal_next2.ml
   OPT:
*/
int x,y,c,d;
void f() {
  int i;
  for(i=0; i<4 ; i++) {
    if (c) { if (d) {y++;} else {x++;}}
    else {};
    x=x+1;
    }
}
