/* run.config
   DONTRUN:
 */

/* run.config_qualif
   OPT:
   OPT: -wp-smoke-tests
   OPT: -wp-smoke-tests -wp-split
*/

/* -------------------------------------------------------------------------- */
// --- All functions shall be proved without smoke tests
// --- All functions « ok » shall pass the smoke tests
// --- All functions « ko » shall reveal dead code
/* -------------------------------------------------------------------------- */

/*@
  ensures \false ;
  exits \false ;
  assigns \nothing ;
 */
void call_ko(void);

/*@
  ensures \true ;
  exits \false ;
  assigns \nothing ;
 */
void call_post_ok(void);

/*@
  ensures \false ;
  exits \true ;
  assigns \nothing ;
 */
void call_exit_ok(void);

int E ;

/*@
  ensures E ;
  exits E ;
  assigns \nothing ;
 */
void call_ko_global(void);

/*@ ensures p ; exits !p ; */
void f1_ok(int p)
{
  if (!p)
    call_exit_ok();
  E++;
}

/*@ ensures p ; exits !p ; */
void f2_ok(int p)
{
  if (p)
    call_post_ok();
  else
    call_exit_ok();
  E++;
}

/*@ ensures E == \old(E)+1 ; */
void f3_ko(void)
{
  call_ko();
  E++;
}

/*@ ensures \false ; */
void f3_ok(void)
{
  call_exit_ok();
}

/*@ ensures E ; */
void f4_ok(void)
{
  E=1;
  call_ko_global();
}

/*@ ensures !E ; */
void f4_ko(void)
{
  E=0;
  call_ko_global();
}

/*@
  ensures E == \old(E)+1 ;
  assigns \nothing ;
 */
void call_wrong(void);

/*@
  ensures E == \old(E)+1 ;
  assigns E ;
 */
void call_effect(void);

/*@
  ensures E == \old(E)+3 ;
*/
void f5_ok(void)
{
  call_effect();
  call_effect();
  call_effect();
}

/*@
  ensures E == \old(E)+3 ;
*/
void f5_ko(void)
{
  call_effect();
  call_wrong();
  call_effect();
}
