/*run.config
  STDOPT: #"-eva-precision 1 -eva-split-return full"
*/
#include "pwd.c"
#include "__fc_string_axiomatic.h"

extern uid_t uid;

int main() {
  struct passwd pwd_out;
  struct passwd *result;
  char buf[320];
  size_t buflen = sizeof(buf);
  int res = getpwuid_r(uid, &pwd_out, buf, buflen, &result);
  if (result) {
    //@ assert res == 0;
    //@ assert \initialized(&pwd_out.pw_uid);
    //@ assert \initialized(&pwd_out.pw_gid);
    //Note: ideally, the following assertions will be 'true' someday
    //@ assert valid_read_string(pwd_out.pw_name);
    //@ assert valid_read_string(pwd_out.pw_passwd);
    //@ assert valid_read_string(pwd_out.pw_dir);
    //@ assert valid_read_string(pwd_out.pw_shell);
  }
  //@ slevel merge;
  struct passwd pwd_out2;
  res = getpwnam_r("root", &pwd_out2, buf, buflen, &result);
  if (result) {
    //@ assert res == 0;
    //@ assert \initialized(&pwd_out2.pw_uid);
    //@ assert \initialized(&pwd_out2.pw_gid);
    //Note: ideally, the following assertions will be 'true' someday
    //@ assert unknown_for_now: valid_read_string(pwd_out2.pw_name);
    //@ assert unknown_for_now: valid_read_string(pwd_out2.pw_passwd);
    //@ assert unknown_for_now: valid_read_string(pwd_out2.pw_dir);
    //@ assert unknown_for_now: valid_read_string(pwd_out2.pw_shell);
  }
}
