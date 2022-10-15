/* run.config
   OPT: -wp-rte -wp-smoke-tests -wp-smoke-dead-local-init
*/

/* run.config_qualif
   OPT: -wp-rte -wp-smoke-tests -wp-smoke-dead-local-init
*/

int access(int *ptr){
  if(ptr) *ptr = 42;
  else *ptr ;
	return 0 ;
}
