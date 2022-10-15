/* run.config
   FILTER: sed -E -e '/atanf_/ s/([0-9][.][0-9]{6})[0-9]+/\1/g'
   STDOPT: #"-warn-special-float none" #"-cpp-extra-args=\"-DNONFINITE\"" #"-eva-slevel 4"
   STDOPT: #"-warn-special-float nan" #"-cpp-extra-args=\"-DNONFINITE -DNONAN\"" #"-eva-slevel 4"
   STDOPT: #"-eva-slevel 4"
*/
#include <math.h>
const double pi = 3.14159265358979323846264338327950288;
const double half_pi = 1.57079632679489661923132169163975144;
const double e = 2.718281828459045090795598298427648842334747314453125;
volatile double top;
const float f_pi = 3.14159265358979323846264338327950288F;
const float f_half_pi = 1.57079632679489661923132169163975144F;
const float f_e = 2.718281828459045090795598298427648842334747314453125F;
volatile float f_top;
const long double ld_pi = 3.14159265358979323846264338327950288L;
const long double ld_half_pi = 1.57079632679489661923132169163975144L;
const long double ld_e = 2.718281828459045090795598298427648842334747314453125L;
volatile long double ld_top;
const double zero = 0.0;
const double minus_zero = -0.0;
const double one = 1.0;
const double minus_one = -1.0;
const double large = 1e38;
#ifdef NONFINITE
const float f_pos_inf = HUGE_VALF;
const double pos_inf = HUGE_VAL;
const long double ld_pos_inf = HUGE_VALL;
const float f_neg_inf = -HUGE_VALF;
const double neg_inf = -HUGE_VAL;
const long double ld_neg_inf = -HUGE_VALL;
const float infinity = INFINITY;
#endif
const double fp_ilogb0 = FP_ILOGB0;
const double fp_ilogbnan = FP_ILOGBNAN;
volatile int int_top;

volatile int nondet;

#define TEST_VAL_CONST(type,f,cst) \
  if (nondet) { type f##_##cst = f(cst); }
#define TEST_FUN_CONSTS(type,f,prefix)          \
  TEST_VAL_CONST(type,f,prefix##pi);            \
  TEST_VAL_CONST(type,f,prefix##half_pi);       \
  TEST_VAL_CONST(type,f,prefix##e);             \
  TEST_VAL_CONST(type,f,zero);                  \
  TEST_VAL_CONST(type,f,minus_zero);            \
  TEST_VAL_CONST(type,f,one);                   \
  TEST_VAL_CONST(type,f,minus_one);             \
  TEST_VAL_CONST(type,f,large);                 \
  TEST_VAL_CONST(type,f,prefix##top)

// tests functions with 2 arguments, where the first one changes,
// but the second one is fixed by the caller.
// suffix prevents redeclaring variables with the same name
#define TEST_VAL2_FST_CONST(type,f,cst,snd_arg,suffix)  \
  if (nondet) { type f##_##cst##suffix = f(cst,snd_arg); }
#define TEST_FUN2_FST_CONSTS(type,f,prefix,snd_arg,suffix)      \
  TEST_VAL2_FST_CONST(type,f,prefix##pi,snd_arg,suffix);        \
  TEST_VAL2_FST_CONST(type,f,prefix##half_pi,snd_arg,suffix);   \
  TEST_VAL2_FST_CONST(type,f,prefix##e,snd_arg,suffix);         \
  TEST_VAL2_FST_CONST(type,f,zero,snd_arg,suffix);              \
  TEST_VAL2_FST_CONST(type,f,minus_zero,snd_arg,suffix);        \
  TEST_VAL2_FST_CONST(type,f,one,snd_arg,suffix);               \
  TEST_VAL2_FST_CONST(type,f,minus_one,snd_arg,suffix);         \
  TEST_VAL2_FST_CONST(type,f,large,snd_arg,suffix);      \
  TEST_VAL2_FST_CONST(type,f,prefix##top,snd_arg,suffix)

#ifdef NONFINITE
#define TEST_FUN_NONFINITE(type,f,prefix)     \
  TEST_VAL_CONST(type,f,prefix##pos_inf);     \
  TEST_VAL_CONST(type,f,prefix##neg_inf)
#else
#define TEST_FUN_NONFINITE(type,f,prefix)
#endif

#define TEST_FUN_ALL_PREC(fun)                  \
  TEST_FUN_CONSTS(double,fun,);                 \
  TEST_FUN_CONSTS(float,fun ## f,f_);           \
  TEST_FUN_CONSTS(long double,fun ## l,ld_);    \
  TEST_FUN_NONFINITE(double,fun,);              \
  TEST_FUN_NONFINITE(float,fun ## f,f_);        \
  TEST_FUN_NONFINITE(long double,fun ## l,ld_)

int main() {
  TEST_FUN_ALL_PREC(atan);
  TEST_FUN_ALL_PREC(fabs);
  TEST_FUN_ALL_PREC(tan);
  int exponent;
  TEST_FUN2_FST_CONSTS(double,frexp,,&exponent,);
  TEST_FUN2_FST_CONSTS(float,frexpf,f_,&exponent,);
  TEST_FUN2_FST_CONSTS(long double,frexpl,ld_,&exponent,);
  TEST_FUN2_FST_CONSTS(double,ldexp,,10,);
  TEST_FUN2_FST_CONSTS(float,ldexpf,f_,10,);
  //TEST_FUN2_FST_CONSTS(long double,ldexpl,ld_,10,);
  TEST_FUN2_FST_CONSTS(double,ldexp,,0,_zero);
  TEST_FUN2_FST_CONSTS(float,ldexpf,f_,0,_zero);
  //TEST_FUN2_FST_CONSTS(long double,ldexpl,ld_,0,_zero);
  TEST_FUN2_FST_CONSTS(double,ldexp,,-5,_minus5);
  TEST_FUN2_FST_CONSTS(float,ldexpf,f_,-5,_minus5);
  //TEST_FUN2_FST_CONSTS(long double,ldexpl,ld_,-5,_minus5);
  TEST_FUN2_FST_CONSTS(double,ldexp,,100000,_pos_inf);
  TEST_FUN2_FST_CONSTS(float,ldexpf,f_,100000,_pos_inf);
  //TEST_FUN2_FST_CONSTS(long double,ldexpl,ld_,100000,_pos_inf);

#ifdef NONFINITE
  int r;
  r = isfinite(pi);
  //@ assert r;
  r = isfinite(large);
  //@ assert r;
  r = isfinite(0.0f);
  //@ assert r;
  r = isfinite(pos_inf);
  //@ assert !r;
  r = isfinite(-INFINITY);
  //@ assert !r;
#ifndef NONAN
  r = isfinite(NAN);
#endif
  //@ assert !r;
#endif
}
