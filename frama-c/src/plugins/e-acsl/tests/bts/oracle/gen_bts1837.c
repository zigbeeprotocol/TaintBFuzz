/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
char *__gen_e_acsl_literal_string_3;
char *__gen_e_acsl_literal_string;
char *__gen_e_acsl_literal_string_2;
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

char *S = (char *)"foo";
int f(void)
{
  int __retres;
  char *s1 = (char *)__gen_e_acsl_literal_string;
  __e_acsl_store_block((void *)(& s1),8UL);
  __e_acsl_full_init((void *)(& s1));
  char *s2 = (char *)__gen_e_acsl_literal_string_2;
  __e_acsl_store_block((void *)(& s2),8UL);
  __e_acsl_full_init((void *)(& s2));
  {
    int __gen_e_acsl_valid_read;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"S",(void *)S);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,"sizeof(char)",
                                   0,sizeof(char));
    __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)S,sizeof(char),
                                                  (void *)S,(void *)(& S));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                 "\\valid_read(S)",0,__gen_e_acsl_valid_read);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "\\valid_read(S)";
    __gen_e_acsl_assert_data.file = "bts1837.i";
    __gen_e_acsl_assert_data.fct = "f";
    __gen_e_acsl_assert_data.line = 11;
    __e_acsl_assert(__gen_e_acsl_valid_read,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert \valid_read(S); */ ;
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"&s1",
                                 (void *)(& s1));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                   "sizeof(char *)",0,sizeof(char *));
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& s1),
                                                    sizeof(char *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "\\initialized(&s1)",0,
                                 __gen_e_acsl_initialized);
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid_read_2;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"s1",
                                   (void *)s1);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                     "sizeof(char)",0,sizeof(char));
      __gen_e_acsl_valid_read_2 = __e_acsl_valid_read((void *)s1,
                                                      sizeof(char),
                                                      (void *)s1,
                                                      (void *)(& s1));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                   "\\valid_read(s1)",0,
                                   __gen_e_acsl_valid_read_2);
      __gen_e_acsl_and = __gen_e_acsl_valid_read_2;
    }
    else __gen_e_acsl_and = 0;
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "\\valid_read(s1)";
    __gen_e_acsl_assert_data_2.file = "bts1837.i";
    __gen_e_acsl_assert_data_2.fct = "f";
    __gen_e_acsl_assert_data_2.line = 12;
    __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
  }
  /*@ assert \valid_read(s1); */ ;
  {
    int __gen_e_acsl_initialized_2;
    int __gen_e_acsl_and_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"&s2",
                                 (void *)(& s2));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                   "sizeof(char *)",0,sizeof(char *));
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)(& s2),
                                                      sizeof(char *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "\\initialized(&s2)",0,
                                 __gen_e_acsl_initialized_2);
    if (__gen_e_acsl_initialized_2) {
      int __gen_e_acsl_valid_read_3;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"s2",
                                   (void *)s2);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                     "sizeof(char)",0,sizeof(char));
      __gen_e_acsl_valid_read_3 = __e_acsl_valid_read((void *)s2,
                                                      sizeof(char),
                                                      (void *)s2,
                                                      (void *)(& s2));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                   "\\valid_read(s2)",0,
                                   __gen_e_acsl_valid_read_3);
      __gen_e_acsl_and_2 = __gen_e_acsl_valid_read_3;
    }
    else __gen_e_acsl_and_2 = 0;
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "\\valid_read(s2)";
    __gen_e_acsl_assert_data_3.file = "bts1837.i";
    __gen_e_acsl_assert_data_3.fct = "f";
    __gen_e_acsl_assert_data_3.line = 13;
    __e_acsl_assert(__gen_e_acsl_and_2,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  /*@ assert \valid_read(s2); */ ;
  __retres = 0;
  __e_acsl_delete_block((void *)(& s2));
  __e_acsl_delete_block((void *)(& s1));
  return __retres;
}

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __gen_e_acsl_literal_string_3 = "toto";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_3,
                         sizeof("toto"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_3);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_3);
    __gen_e_acsl_literal_string = "foo";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string,sizeof("foo"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string);
    __gen_e_acsl_literal_string_2 = "bar";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_2,sizeof("bar"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_2);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_2);
    __e_acsl_store_block((void *)(& S),8UL);
    __e_acsl_full_init((void *)(& S));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& S));
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  int i = 4;
  while (1) {
    int tmp;
    tmp = i;
    i --;
    ;
    if (! tmp) break;
    {
      char *s = (char *)__gen_e_acsl_literal_string_3;
      __e_acsl_store_block((void *)(& s),8UL);
      __e_acsl_full_init((void *)(& s));
      {
        int __gen_e_acsl_initialized;
        int __gen_e_acsl_and;
        __e_acsl_assert_data_t __gen_e_acsl_assert_data =
          {.values = (void *)0};
        __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"&s",
                                     (void *)(& s));
        __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                       "sizeof(char *)",0,sizeof(char *));
        __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& s),
                                                        sizeof(char *));
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                     "\\initialized(&s)",0,
                                     __gen_e_acsl_initialized);
        if (__gen_e_acsl_initialized) {
          int __gen_e_acsl_valid_read;
          __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"s",
                                       (void *)s);
          __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                         "sizeof(char)",0,sizeof(char));
          __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)s,
                                                        sizeof(char),
                                                        (void *)s,
                                                        (void *)(& s));
          __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                       "\\valid_read(s)",0,
                                       __gen_e_acsl_valid_read);
          __gen_e_acsl_and = __gen_e_acsl_valid_read;
        }
        else __gen_e_acsl_and = 0;
        __gen_e_acsl_assert_data.blocking = 1;
        __gen_e_acsl_assert_data.kind = "Assertion";
        __gen_e_acsl_assert_data.pred_txt = "\\valid_read(s)";
        __gen_e_acsl_assert_data.file = "bts1837.i";
        __gen_e_acsl_assert_data.fct = "main";
        __gen_e_acsl_assert_data.line = 21;
        __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data);
        __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
      }
      /*@ assert \valid_read(s); */ ;
      {
        int __gen_e_acsl_initialized_2;
        int __gen_e_acsl_and_2;
        __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
          {.values = (void *)0};
        __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"&s",
                                     (void *)(& s));
        __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                       "sizeof(char *)",0,sizeof(char *));
        __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)(& s),
                                                          sizeof(char *));
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                     "\\initialized(&s)",0,
                                     __gen_e_acsl_initialized_2);
        if (__gen_e_acsl_initialized_2) {
          int __gen_e_acsl_valid;
          __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"s",
                                       (void *)s);
          __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                         "sizeof(char)",0,sizeof(char));
          __gen_e_acsl_valid = __e_acsl_valid((void *)s,sizeof(char),
                                              (void *)s,(void *)(& s));
          __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                       "\\valid(s)",0,__gen_e_acsl_valid);
          __gen_e_acsl_and_2 = __gen_e_acsl_valid;
        }
        else __gen_e_acsl_and_2 = 0;
        __gen_e_acsl_assert_data_2.blocking = 1;
        __gen_e_acsl_assert_data_2.kind = "Assertion";
        __gen_e_acsl_assert_data_2.pred_txt = "!\\valid(s)";
        __gen_e_acsl_assert_data_2.file = "bts1837.i";
        __gen_e_acsl_assert_data_2.fct = "main";
        __gen_e_acsl_assert_data_2.line = 22;
        __e_acsl_assert(! __gen_e_acsl_and_2,& __gen_e_acsl_assert_data_2);
        __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
      }
      /*@ assert !\valid(s); */ ;
      __e_acsl_delete_block((void *)(& s));
    }
  }
  f();
  __retres = 0;
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return __retres;
}


