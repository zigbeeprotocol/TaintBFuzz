/* run.config*
   OPT: -eva @EVA_CONFIG@ -warn-special-float non-finite
   OPT: -eva @EVA_CONFIG@ -warn-special-float nan
   OPT: -eva @EVA_CONFIG@ -warn-special-float none
*/

/*@
  assigns \result \from x;
  behavior normal:
    assumes domain_arg: \is_plus_infinity(x) || (\is_finite(x) && x >= 1.);
    ensures finite_result: \is_finite(\result);
    ensures positive_result: \result >= 0.;
  behavior negative:
    assumes negative_arg: \is_minus_infinity(x) || (\is_finite(x) && x < 0.);
    ensures nan_result: \is_NaN(\result);
  behavior infinite:
    assumes small_arg: \is_finite(x) && x >= 0. && x < 1.;
    ensures infinite_result: \is_plus_infinity(\result);
  behavior nan:
    assumes nan_arg: \is_NaN(x);
    ensures nan_result: \is_NaN(\result);
  complete behaviors;
  disjoint behaviors;
*/
extern double fun(double x);

/*@
  behavior normal:
    assumes domain_arg: \is_plus_infinity(x) || (\is_finite(x) && x >= 1.);
    assigns \result \from x;
    ensures finite_result: \is_finite(\result);
    ensures positive_result: \result >= 0.;
  behavior negative:
    assumes negative_arg: \is_minus_infinity(x) || (\is_finite(x) && x < 0.);
    assigns \result \from x;
    ensures nan_result: \is_NaN(\result);
  behavior infinite:
    assumes small_arg: \is_finite(x) && x >= 0. && x < 1.;
    assigns \result \from x;
    ensures infinite_result: \is_plus_infinity(\result);
  behavior nan:
    assumes nan_arg: \is_NaN(x);
    assigns \result \from x;
    ensures nan_result: \is_NaN(\result);
  complete behaviors;
  disjoint behaviors;
*/
extern double fun_no_default(double x);

/*@
  assigns \result \from x;
  behavior normal:
    assumes domain_arg: \is_plus_infinity(x) || (\is_finite(x) && x >= 1.);
    ensures finite_result: \is_finite(\result);
    ensures positive_result: \result >= 0.;
  behavior negative:
    assumes negative_arg: \is_minus_infinity(x) || (\is_finite(x) && x < 0.);
    ensures nan_result: \is_NaN(\result);
  behavior infinite:
    assumes small_arg: \is_finite(x) && x >= 0. && x < 1.;
    ensures infinite_result: \is_plus_infinity(\result);
  behavior nan:
    assumes nan_arg: \is_NaN(x);
    ensures nan_result: \is_NaN(\result);
  complete behaviors;
*/
extern double fun_no_disjoint(double x);

/*@
  assigns \result \from x;
  behavior normal:
    assumes domain_arg: \is_plus_infinity(x) || (\is_finite(x) && x >= 1.);
    ensures finite_result: \is_finite(\result);
    ensures positive_result: \result >= 0.;
  behavior negative:
    assumes negative_arg: \is_minus_infinity(x) || (\is_finite(x) && x < 0.);
    ensures nan_result: \is_NaN(\result);
  behavior infinite:
    assumes small_arg: \is_finite(x) && x >= 0. && x < 1.;
    ensures infinite_result: \is_plus_infinity(\result);
  behavior nan:
    assumes nan_arg: \is_NaN(x);
    ensures nan_result: \is_NaN(\result);
  disjoint behaviors;
*/
extern double fun_no_complete(double x);

volatile double v;

int main(){
  double a = v;
  double w = fun(a);
  double b = v;
  double x = fun_no_default(b); // no default behavior
  double c = v;
  double y = fun_no_disjoint(c); // no disjoint behaviors
  double d = v;
  double z = fun_no_complete(d); // no complete behaviors
}
