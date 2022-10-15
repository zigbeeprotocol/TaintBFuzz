/* run.config
   COMMENT: run.config is intentionally not-*
 PLUGIN:
   EXECNOW: BIN absorb.sav LOG absorb_sav.res LOG absorb_sav.err @frama-c@ -save @PTEST_RESULT@/absorb.sav @PTEST_FILE@ > @PTEST_RESULT@/absorb_sav.res 2> @PTEST_RESULT@/absorb_sav.err
 PLUGIN: @EVA_PLUGINS@
   EXECNOW: BIN absorb.sav2 LOG absorb_sav2.res LOG absorb_sav2.err @frama-c@ -load %{dep:@PTEST_RESULT@/absorb.sav} -eva @EVA_CONFIG@ -float-hex -save @PTEST_RESULT@/absorb.sav2 > @PTEST_RESULT@/absorb_sav2.res 2> @PTEST_RESULT@/absorb_sav2.err
 COMMENT: the following CMD redefinition omits adding @PTEST_FILE@ on purpose.
 CMD: @frama-c@ @PTEST_OPTIONS@
   OPT: -load %{dep:@PTEST_RESULT@/absorb.sav2} -deps -out -input
*/
/* run.config*
   DONTRUN:
*/
#include "__fc_builtin.h"

float x = 1.0, y = 0.0, z, t, min_f, min_fl, den;

void main() {
  long long b = Frama_C_interval(-2000000001, 2000000001);
  b = b * b;
  z = y + 1e-286;
  while (y != x)
  {
    y = x ; x+=1E-286;
  }
  t = b;
  min_f = 1.175494351e-38;
  min_fl = -1.1754943505e-38;
  den = min_f / 128.;
}
