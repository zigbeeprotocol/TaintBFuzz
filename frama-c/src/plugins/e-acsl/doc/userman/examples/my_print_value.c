#include <stdio.h>
#include <e_acsl.h>

void __e_acsl_print_value(__e_acsl_assert_data_value_t * value) {
  printf("\t- custom print for %s\n", value->name);
}
