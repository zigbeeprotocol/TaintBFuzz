/* run.config
   DONTRUN:
 */

/* run.config_qualif
   OPT: -wp-smoke-tests -wp-steps 100
   OPT: -wp-smoke-tests -wp-steps 100 -wp-split
*/

//@ assigns \nothing ;
int f1_ok(int x)
{
  int r ;
  if (x) r++;
  if (x) r++;
  return r;
}

/*@
  ensures \false ;
  exits \true ;
  assigns \nothing ;
*/
void exit(void);

/*@
  assigns \nothing ;
*/
void call(void);

//@ assigns \nothing ;
int f2_ok(int x)
{
  int r ;
  if (x) { exit(); }
  r++;
  return r;
}

//@ assigns \nothing ;
int f2_ko(int x)
{
  int r ;
  if (x) { exit(); r++; }
  return r;
}

//@ assigns \nothing ;
int f3_ok(int x)
{
  int r ;
  if (x) { call(); r++; }
  return r;
}

//@ assigns \nothing ;
int f4_ok(int x)
{
  int r ;
  if (x) {
    exit();
    //@ assert \false ;
    r++;
  } else {
    r++;
  }
  return r;
}

//@ assigns \nothing ;
int f5_ok(int op,int a)
{
  switch(op) {
  case 1:
  case 2:
    return a+1;
  case 3:
    return a-1;
  default:
    return a;
  }
}

//@ assigns \nothing ;
int f5_ko(int op,int a)
{
  if (op == 1) return 0;
  switch(op) {
  case 1:
    return a+1;
  case 2:
    return a-1;
  default:
    return a;
  }
}
