/* run.config
   STDOPT: #"-eva-slevel 4"
 */

#include <time.h>
#include "__fc_builtin.h"


int main() {
  struct timespec req, rem;
  req.tv_sec = 42;
  req.tv_nsec = 9001;
  int r = nanosleep(&req, &rem);
  while (r) {
    if (errno == EINTR) {
      req = rem;
      r = nanosleep(&req, &rem);
    } else {
      return 1;
    }
  }
  r = nanosleep(&req, 0);
  if (r) return 2;

  struct timespec creq, crem;
  creq.tv_sec = 42;
  creq.tv_nsec = 9001;
  clock_nanosleep(CLOCK_REALTIME, TIMER_ABSTIME, &creq, &crem);
  //@ assert !\initialized(&crem);
  clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &creq, 0);

  r = clock_nanosleep(CLOCK_MONOTONIC, 0, &creq, &crem);
  while (r) {
    if (errno == EINTR) {
      creq = crem;
      r = clock_nanosleep(CLOCK_MONOTONIC, 0, &creq, &crem);
    } else {
      return 1;
    }
  }

  time_t tt = 42;
  char *time_str = ctime(&tt);
  //@ assert valid_string(time_str);

  struct tm mytime =
    {
     .tm_sec = Frama_C_interval(0,60), // 60: for leap seconds
     .tm_min = Frama_C_interval(0,59),
     .tm_hour = Frama_C_interval(0,23),
     .tm_mday = Frama_C_interval(1,31),
     .tm_mon = Frama_C_interval(0,11),
     .tm_year = Frama_C_interval(0,177), // arbitrary value
     .tm_wday = Frama_C_interval(0,6),
     .tm_yday = Frama_C_interval(0,365),
     .tm_isdst = Frama_C_interval(0,1)
    };
  time_t t = mktime(&mytime);
  struct tm *res_time;
  res_time = gmtime(&t);
  struct tm mytime2;
  res_time = gmtime_r(&t, &mytime2);

  time_str = asctime(&mytime);
  //@ assert valid_string(time_str);

  struct tm *localp = localtime(&t);
  struct tm localr;
  localp = localtime_r(&t, &localr);
  //@ assert localp == \null || localp == &localr;

  return 0;
}
