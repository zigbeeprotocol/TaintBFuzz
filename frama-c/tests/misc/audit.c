/* run.config
 PLUGIN: @EVA_PLUGINS@
   EXECNOW: BIN audit.json cat %{dep:@PTEST_DIR@/audit-in.json} | sed -e 's:PTEST_DIR:@PTEST_DIR@:' > @PTEST_RESULT@/audit.json 2> @DEV_NULL@
 DEPS: audit_included.h, audit_included_but_not_listed.h
 LOG: audit-out.json
   STDOPT: #"-audit-check %{dep:@PTEST_RESULT@/audit.json} -audit-prepare @PTEST_RESULT@/audit-out.json -kernel-warn-key audit=active"
*/
#include "audit_included.h"
#include "audit_included_but_not_listed.h"

void main() {
  float f = 2.1; // to trigger a syntactic warning
}
