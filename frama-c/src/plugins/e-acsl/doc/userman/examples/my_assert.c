#include <stdio.h>
#include <e_acsl.h>

extern int __e_acsl_sound_verdict;

void __e_acsl_assert(int predicate, __e_acsl_assert_data_t * data) {
  printf("%s in file %s at line %d in function %s is %s (%s).\n\
The verified predicate was: `%s'.\n",
    data->kind,
    data->file,
    data->line,
    data->fct,
    predicate ? "valid" : "invalid",
    __e_acsl_sound_verdict ? "trustworthy" : "UNTRUSTWORTHY",
    data->pred_txt);
  if (data->values) {
    printf("With values:\n");
    __e_acsl_assert_data_value_t * value = data->values;
    while (value != NULL) {
      __e_acsl_print_value(value);
      value = value->next;
    }
  }
}
