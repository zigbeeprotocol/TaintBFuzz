/* run.config
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose (due to -load)
 CMD: @frama-c@ @PTEST_OPTIONS@
 COMMENT: do not compare generated journals since they depend on current time
 PLUGIN: @EVA_PLUGINS@
   EXECNOW: BIN control_journal.ml @frama-c@ @PTEST_FILE@ -journal-enable -eva -deps -out @EVA_OPTIONS@ -main f -journal-name @PTEST_RESULT@/control_journal.ml > @DEV_NULL@ 2> @DEV_NULL@
 SCRIPT: @PTEST_RESULT@/control_journal.ml
   OPT:
 MODULE:
 SCRIPT: @PTEST_RESULT@/control_journal_bis.ml
   EXECNOW: BIN control_journal_bis.ml cp %{dep:@PTEST_RESULT@/control_journal.ml} @PTEST_RESULT@/control_journal_bis.ml > @DEV_NULL@ 2> @DEV_NULL@
   OPT: -calldeps
 MODULE: abstract_cpt use_cpt
 SCRIPT:
   EXECNOW: BIN abstract_cpt_journal.ml @frama-c@ -journal-enable -journal-name @PTEST_RESULT@/abstract_cpt_journal.ml > @DEV_NULL@ 2> @DEV_NULL@
 SCRIPT: @PTEST_RESULT@/abstract_cpt_journal.ml
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
