/* run.config*
PLUGIN: @EVA_MAIN_PLUGINS@ report rtegen
   OPT: -machdep x86_32 @RTE_TEST@ -then -eva @EVA_CONFIG@ -then -report -report-print-properties
   OPT: -machdep x86_32 -eva @EVA_CONFIG@ -then @RTE_TEST@  -then -report -report-print-properties
*/
// Fuse with precond.c when bts #1208 is solved
int x;

/*@ requires i_plus_one: i+1 >= 0;
  requires i: i >= 0;
  assigns x; */
void f (int i) {
  x = i;
}

//@ requires x <= 8;
void g(void);

void main (int c) {
  if (c) {
    f(1);
    if(c) f(-1);
  }
  g ();g ();
}
