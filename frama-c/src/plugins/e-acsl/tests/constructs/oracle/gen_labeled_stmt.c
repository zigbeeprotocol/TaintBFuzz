/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

int X = 0;
/*@ ensures X == 3; */
int main(void);

int __gen_e_acsl_main(void)
{
  int __retres;
  goto L1;
  L1:
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"X",0,X);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "X == 0";
    __gen_e_acsl_assert_data.file = "labeled_stmt.i";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 10;
    __e_acsl_assert(X == 0,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert X == 0; */ ;
  X = 1;
  goto L2;
  L2:
  {
    {
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,"X",0,X);
      __gen_e_acsl_assert_data_2.blocking = 1;
      __gen_e_acsl_assert_data_2.kind = "Precondition";
      __gen_e_acsl_assert_data_2.pred_txt = "X == 1";
      __gen_e_acsl_assert_data_2.file = "labeled_stmt.i";
      __gen_e_acsl_assert_data_2.fct = "main";
      __gen_e_acsl_assert_data_2.line = 13;
      __e_acsl_assert(X == 1,& __gen_e_acsl_assert_data_2);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    }
    /*@ requires X == 1;
        ensures X == 2; */
    X = 2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,"X",0,X);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Postcondition";
    __gen_e_acsl_assert_data_3.pred_txt = "X == 2";
    __gen_e_acsl_assert_data_3.file = "labeled_stmt.i";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 13;
    __e_acsl_assert(X == 2,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  if (X) {
    X = 3;
    __retres = 0;
    goto return_label;
  }
  __retres = 0;
  return_label: return __retres;
}

/*@ ensures X == 3; */
int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __retres = __gen_e_acsl_main();
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"X",0,X);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Postcondition";
    __gen_e_acsl_assert_data.pred_txt = "X == 3";
    __gen_e_acsl_assert_data.file = "labeled_stmt.i";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 7;
    __e_acsl_assert(X == 3,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __e_acsl_memory_clean();
    return __retres;
  }
}


