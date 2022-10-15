/* run.config_qualif
   OPT: -wp-steps 100
 */

_Bool A, B;

/*@
  ensures GOAL: \result ≡ 255;
 */
unsigned job(void)
{
  _Bool a0;
  _Bool a1;
  _Bool a2;
  _Bool a3;
  _Bool a4;
  _Bool a5;
  _Bool a6;
  _Bool a7;
  a0 = 1;
  a1 = 1;
  a2 = 1;
  a4 = 1;
  a3 = 1;
  a5 = 1;
  a6 = A;
  a7 = B;
  //*integrity_tests =
  return
    ((unsigned int)a0 << 0) |
    ((unsigned int)a1 << 1) |
    ((unsigned int)a2 << 2) |
    ((unsigned int)a3 << 3) |
    ((unsigned int)a4 << 4) |
    ((unsigned int)a5 << 5) |
    ((unsigned int)a6 << 6) |
    ((unsigned int)a7 << 7);
}
