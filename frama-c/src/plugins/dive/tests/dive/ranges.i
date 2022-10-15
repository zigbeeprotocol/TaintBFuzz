/* run.config
STDOPT: +"-dive-from-variables main::res -dive-depth-limit 4 -kernel-warn-key parser:decimal-float=inactive"
*/

/*@ assigns \result \from min, max;
    ensures result_bounded: min <= \result <= max ;
 */
extern int Frama_C_interval(int min, int max);

/*@ assigns \result \from min, max;
    ensures result_bounded: \is_finite(\result) && min <= \result <= max;
 */
extern float Frama_C_float_interval(float min, float max);

float main()
{
  int i0 = 2;
  int i1 = Frama_C_interval(0, 3);
  int i2 = Frama_C_interval(0, 12);
  int i3 = Frama_C_interval(0, 127);
  int i4 = Frama_C_interval(0, 42000);
  int i5 = Frama_C_interval(0, 1350000);
  int i6 = Frama_C_interval(0, 910000000);
  int i7 = Frama_C_interval(0, 2000000000);
  int i = i0 + i1 + i2 + i3 + i4 + i5 + i6 + i7;

  float f0 = 0.;
  float f1 = Frama_C_float_interval(0.f, 0.001f);
  float f2 = Frama_C_float_interval(0.f, 3.14f);
  float f3 = Frama_C_float_interval(0.f, 1020.f);
  float f4 = Frama_C_float_interval(0.f, 1e7f);
  float f5 = Frama_C_float_interval(0.f, 1e20f);
  float f6 = Frama_C_float_interval(0.f, 1e36f);
  float f7 = Frama_C_float_interval(0.f, 1e37f);
  float f = f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7;

  float res = i + f;
  return res;
}
