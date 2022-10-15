/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

/*@ assigns *timer, \result;
    assigns *timer \from __fc_time;
    assigns \result \from __fc_time;
    
    behavior null:
      assumes timer_null: timer == \null;
      assigns \result;
      assigns \result \from __fc_time;
    
    behavior not_null:
      assumes timer_non_null: timer != \null;
      requires valid_timer: \valid(timer);
      ensures initialization: timer: \initialized(\old(timer));
      assigns *timer, \result;
      assigns *timer \from __fc_time;
      assigns \result \from __fc_time;
    
    complete behaviors not_null, null;
    disjoint behaviors not_null, null;
 */
time_t __gen_e_acsl_time(time_t *timer);

/*@ assigns *timer, \result;
    assigns *timer \from __fc_time;
    assigns \result \from __fc_time;
    
    behavior null:
      assumes timer_null: timer == \null;
      assigns \result;
      assigns \result \from __fc_time;
    
    behavior not_null:
      assumes timer_non_null: timer != \null;
      requires valid_timer: \valid(timer);
      ensures initialization: timer: \initialized(\old(timer));
      assigns *timer, \result;
      assigns *timer \from __fc_time;
      assigns \result \from __fc_time;
    
    complete behaviors not_null, null;
    disjoint behaviors not_null, null;
 */
time_t __gen_e_acsl_time(time_t *timer)
{
  __e_acsl_contract_t *__gen_e_acsl_contract;
  time_t *__gen_e_acsl_at;
  time_t __retres;
  __e_acsl_store_block((void *)(& __retres),8UL);
  {
    int __gen_e_acsl_assumes_value;
    int __gen_e_acsl_active_bhvrs;
    __e_acsl_store_block((void *)(& timer),8UL);
    __gen_e_acsl_at = timer;
    __gen_e_acsl_contract = __e_acsl_contract_init(2UL);
    __e_acsl_contract_set_behavior_assumes(__gen_e_acsl_contract,0UL,
                                           timer == (time_t *)0);
    __e_acsl_contract_set_behavior_assumes(__gen_e_acsl_contract,1UL,
                                           timer != (time_t *)0);
    __gen_e_acsl_assumes_value = __e_acsl_contract_get_behavior_assumes
    ((__e_acsl_contract_t const *)__gen_e_acsl_contract,1UL);
    if (__gen_e_acsl_assumes_value) {
      int __gen_e_acsl_valid;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data =
        {.values = (void *)0};
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"timer",
                                   (void *)timer);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                     "sizeof(time_t)",0,sizeof(time_t));
      __gen_e_acsl_valid = __e_acsl_valid((void *)timer,sizeof(time_t),
                                          (void *)timer,(void *)(& timer));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                   "\\valid(timer)",0,__gen_e_acsl_valid);
      __gen_e_acsl_assert_data.blocking = 1;
      __gen_e_acsl_assert_data.kind = "Precondition";
      __gen_e_acsl_assert_data.pred_txt = "\\valid(timer)";
      __gen_e_acsl_assert_data.file = "FRAMAC_SHARE/libc/time.h";
      __gen_e_acsl_assert_data.fct = "time";
      __gen_e_acsl_assert_data.line = 102;
      __gen_e_acsl_assert_data.name = "not_null/valid_timer";
      __e_acsl_assert(__gen_e_acsl_valid,& __gen_e_acsl_assert_data);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    }
    __gen_e_acsl_active_bhvrs = __e_acsl_contract_partial_count_all_behaviors
    ((__e_acsl_contract_t const *)__gen_e_acsl_contract);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "number of active behaviors",0,
                                 __gen_e_acsl_active_bhvrs);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "number of active behaviors",0,
                                 __gen_e_acsl_active_bhvrs);
    if (__gen_e_acsl_active_bhvrs != 1) {
      __gen_e_acsl_assert_data_2.blocking = 1;
      __gen_e_acsl_assert_data_2.kind = "Precondition";
      __gen_e_acsl_assert_data_2.pred_txt = "all behaviors complete";
      __gen_e_acsl_assert_data_2.file = "FRAMAC_SHARE/libc/time.h";
      __gen_e_acsl_assert_data_2.fct = "time";
      __gen_e_acsl_assert_data_2.line = 95;
      __e_acsl_assert(__gen_e_acsl_active_bhvrs >= 1,
                      & __gen_e_acsl_assert_data_2);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
      __gen_e_acsl_assert_data_3.blocking = 1;
      __gen_e_acsl_assert_data_3.kind = "Precondition";
      __gen_e_acsl_assert_data_3.pred_txt = "all behaviors disjoint";
      __gen_e_acsl_assert_data_3.file = "FRAMAC_SHARE/libc/time.h";
      __gen_e_acsl_assert_data_3.fct = "time";
      __gen_e_acsl_assert_data_3.line = 95;
      __e_acsl_assert(__gen_e_acsl_active_bhvrs <= 1,
                      & __gen_e_acsl_assert_data_3);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
    }
  }
  __retres = time(timer);
  {
    int __gen_e_acsl_assumes_value_2;
    __gen_e_acsl_assumes_value_2 = __e_acsl_contract_get_behavior_assumes
    ((__e_acsl_contract_t const *)__gen_e_acsl_contract,1UL);
    if (__gen_e_acsl_assumes_value_2) {
      int __gen_e_acsl_initialized;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
        {.values = (void *)0};
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_4,
                                   "\\old(timer)",(void *)__gen_e_acsl_at);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_4,
                                     "sizeof(time_t)",0,sizeof(time_t));
      __gen_e_acsl_initialized = __e_acsl_initialized((void *)__gen_e_acsl_at,
                                                      sizeof(time_t));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_4,
                                   "not_null: initialization: timer: \\initialized(\\old(timer))",
                                   0,__gen_e_acsl_initialized);
      __gen_e_acsl_assert_data_4.blocking = 1;
      __gen_e_acsl_assert_data_4.kind = "Postcondition";
      __gen_e_acsl_assert_data_4.pred_txt = "\\initialized(\\old(timer))";
      __gen_e_acsl_assert_data_4.file = "FRAMAC_SHARE/libc/time.h";
      __gen_e_acsl_assert_data_4.fct = "time";
      __gen_e_acsl_assert_data_4.line = 104;
      __gen_e_acsl_assert_data_4.name = "not_null/initialization/timer";
      __e_acsl_assert(__gen_e_acsl_initialized,& __gen_e_acsl_assert_data_4);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_4);
    }
    __e_acsl_contract_clean(__gen_e_acsl_contract);
    __e_acsl_delete_block((void *)(& timer));
    __e_acsl_delete_block((void *)(& __retres));
    return __retres;
  }
}

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __e_acsl_store_block((void *)(& __gen_e_acsl_time),1UL);
    __e_acsl_full_init((void *)(& __gen_e_acsl_time));
    __e_acsl_store_block((void *)(& __fc_interrupted),4UL);
    __e_acsl_full_init((void *)(& __fc_interrupted));
    __e_acsl_store_block((void *)(& __fc_p_time_tm),8UL);
    __e_acsl_full_init((void *)(& __fc_p_time_tm));
    __e_acsl_store_block((void *)(& __fc_time_tm),36UL);
    __e_acsl_full_init((void *)(& __fc_time_tm));
    __e_acsl_store_block((void *)(& __fc_p_ctime),8UL);
    __e_acsl_full_init((void *)(& __fc_p_ctime));
    __e_acsl_store_block((void *)(__fc_ctime),26UL);
    __e_acsl_full_init((void *)(& __fc_ctime));
    __e_acsl_store_block((void *)(& time),1UL);
    __e_acsl_full_init((void *)(& time));
    __e_acsl_store_block((void *)(& __fc_time),4UL);
    __e_acsl_full_init((void *)(& __fc_time));
    __e_acsl_store_block((void *)(& __fc_p_sigaction),8UL);
    __e_acsl_full_init((void *)(& __fc_p_sigaction));
    __e_acsl_store_block((void *)(sigaction),2080UL);
    __e_acsl_full_init((void *)(& sigaction));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& __gen_e_acsl_time));
  __e_acsl_delete_block((void *)(& __fc_interrupted));
  __e_acsl_delete_block((void *)(& __fc_p_time_tm));
  __e_acsl_delete_block((void *)(& __fc_time_tm));
  __e_acsl_delete_block((void *)(& __fc_p_ctime));
  __e_acsl_delete_block((void *)(__fc_ctime));
  __e_acsl_delete_block((void *)(& time));
  __e_acsl_delete_block((void *)(& __fc_time));
  __e_acsl_delete_block((void *)(& __fc_p_sigaction));
  __e_acsl_delete_block((void *)(sigaction));
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(& __retres),4UL);
  time_t tmp = __gen_e_acsl_time((time_t *)0);
  __e_acsl_store_block((void *)(& tmp),8UL);
  __e_acsl_full_init((void *)(& tmp));
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_long(& __gen_e_acsl_assert_data,"tmp",0,tmp);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "tmp != -1";
    __gen_e_acsl_assert_data.file = "vdso.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 13;
    __e_acsl_assert(tmp != -1L,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert tmp != -1; */ ;
  __e_acsl_full_init((void *)(& __retres));
  __retres = 0;
  __e_acsl_delete_block((void *)(& tmp));
  __e_acsl_delete_block((void *)(& __retres));
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return __retres;
}

