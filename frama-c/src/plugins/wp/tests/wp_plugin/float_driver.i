/* run.config
   OPT:-wp -wp-gen -wp-prover why3 -wp-msg-key="print-generated"
*/
/* run.config_qualif
   DONTRUN:
*/

/*@
  ensures DBL_RNE:  \eq_double(\result,\round_double(\NearestEven, x));
  ensures DBL_RNA:  \eq_double(\result,\round_double(\NearestAway, x));
  ensures DBL_RTZ:  \eq_double(\result,\round_double(\ToZero, x));
  ensures DBL_RTP:  \eq_double(\result,\round_double(\Up, x));
  ensures DBL_RTN:  \eq_double(\result,\round_double(\Down, x));
  ensures DBL_FIN:  \is_finite(\result);
  ensures DBL_INF:  \is_infinite(\result);
  ensures DBL_NAN:  \is_NaN(\result);
  ensures DBL_PINF: \is_plus_infinity(\result);
  ensures DBL_MINF: \is_minus_infinity(\result);
*/
double for_double(double x) {
  return x+1.0;
}

/*@
  ensures FLT_RNE:  \eq_float(\result,\round_float(\NearestEven, x));
  ensures FLT_RNA:  \eq_float(\result,\round_float(\NearestAway, x));
  ensures FLT_RTZ:  \eq_float(\result,\round_float(\ToZero, x));
  ensures FLT_RTP:  \eq_float(\result,\round_float(\Up, x));
  ensures FLT_RTN:  \eq_float(\result,\round_float(\Down, x));
  ensures FLT_FIN:  \is_finite(\result);
  ensures FLT_INF:  \is_infinite(\result);
  ensures FLT_NAN:  \is_NaN(\result);
  ensures FLT_PINF: \is_plus_infinity(\result);
  ensures FLT_MINF: \is_minus_infinity(\result);
*/
float for_float(float x) {
  return x+1.0f;
}

