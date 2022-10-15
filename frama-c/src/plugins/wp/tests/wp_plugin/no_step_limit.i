/* run.config
  DONTRUN:
*/
/* run.config_qualif
 DEPS: @PTEST_NAME@.conf
  CMD: WHY3CONFIG=@PTEST_DIR@/@PTEST_NAME@.conf @frama-c@
  OPT: -wp -wp-prover no-steps -wp-steps 10 -wp-timeout 1 -wp-cache none -wp-no-cache-env -wp-msg-key shell
*/

// cache is locally deactivated to see the option

/*@
  lemma truc: \false ;
*/
