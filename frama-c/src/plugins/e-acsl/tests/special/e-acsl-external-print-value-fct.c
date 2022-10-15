/* run.config, run.config_dev
   DONTRUN:
   COMMENT: Support file for e-acsl-external-print-value.c
*/
#include <e_acsl.h>
#include <stdio.h>

void __e_acsl_print_value(__e_acsl_assert_data_value_t *value) {
  fprintf(stderr, "\t- custom print for %s\n", value->name);
}
