/* run.config
   COMMENT: Change order of options to run Eva before E-ACSL so that the ensures
   COMMENT: clause is proven invalid before running E-ACSL. Eva will prove the
   COMMENT: ensures invalid under hypotheses of reachability, this test shows
   COMMENT: that when we duplicate the invalid property statuses, we remove the
   COMMENT: hypotheses to satisfy kernel invariants.
   OPT: @GLOBAL@ @EVA@ -then @EACSL@ -then-last @EVENTUALLY@
*/
/* run.config_dev
   COMMENT: No need to compile and execute the test since we know the property
   COMMENT: will be invalid.
   DONTRUN:
*/

/*@ ensures \result == 1; */
int f() {
  return 0;
}

int main() {
  f();
  return 0;
}
