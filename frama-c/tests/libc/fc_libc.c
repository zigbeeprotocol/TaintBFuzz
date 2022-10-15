/* run.config*
 PLUGIN: @EVA_PLUGINS@ metrics
 EXECNOW: BIN @PTEST_NAME@.sav LOG @PTEST_NAME@_sav.res LOG @PTEST_NAME@_sav.err @frama-c@ -cpp-extra-args='-nostdinc -I@FRAMAC_SHARE@/libc' @PTEST_FILE@ -save @PTEST_NAME@.sav >@PTEST_NAME@_sav.res 2>@PTEST_NAME@_sav.err
 MODULE: check_libc_naming_conventions, check_const
   OPT: -load %{dep:@PTEST_NAME@.sav} -print -cpp-extra-args='-nostdinc -I@FRAMAC_SHARE@/libc' -eva @EVA_CONFIG@ -then -lib-entry -no-print
 MODULE:
   OPT: -print -print-libc -machdep x86_32
 MODULE: check_parsing_individual_headers
   OPT:
 MODULE: check_libc_anonymous_tags
   OPT:
 MODULE: check_compliance
   OPT: -kernel-msg-key printer:attrs
 MODULE:
   OPT: -load %{dep:@PTEST_NAME@.sav} -metrics -metrics-libc -then -lib-entry -metrics-no-libc | %{dep:./check_some_metrics.sh} "> 100" "> 400" "< 2" "> 0" "= 1" "= 1" "= 0" "= 0" "= 0" "= 1"
 CMD: %{dep:./check_full_libc.sh} @FRAMAC_SHARE@/libc
   OPT:
**/


#define __FC_REG_TEST
// Some functions such as usleep() are only defined for older of POSIX headers,
// while others may be defined only by newer ones, so it is not possible to
// test all of them. We nevertheless define some headers to test additional
// functions.
#define _XOPEN_SOURCE 600
#define _POSIX_C_SOURCE 200112L
#define _GNU_SOURCE 1

#include "__fc_runtime.c"

#include "aio.h"
#include "alloca.h"
#include "argz.h"
#include "arpa/inet.h"
#include "assert.h"
#include "byteswap.h"
#include "complex.h"
#include "cpio.h"
#include "ctype.h"
#include "dirent.h"
#include "dlfcn.h"
#include "endian.h"
#include "err.h"
#include "errno.h"
#include "__fc_alloc_axiomatic.h"
#include "__fc_builtin.h"
#include "__fc_define_blkcnt_t.h"
#include "__fc_define_blksize_t.h"
#include "__fc_define_clockid_t.h"
#include "__fc_define_dev_t.h"
#include "__fc_define_eof.h"
#include "__fc_define_fd_set_t.h"
#include "__fc_define_fds.h"
#include "__fc_define_file.h"
#include "__fc_define_fpos_t.h"
#include "__fc_define_fs_cnt.h"
#include "__fc_define_id_t.h"
#include "__fc_define_ino_t.h"
#include "__fc_define_intptr_t.h"
#include "__fc_define_iovec.h"
#include "__fc_define_key_t.h"
#include "__fc_define_locale_t.h"
#include "__fc_define_max_open_files.h"
#include "__fc_define_mode_t.h"
#include "__fc_define_nlink_t.h"
#include "__fc_define_null.h"
#include "__fc_define_off_t.h"
#include "__fc_define_pid_t.h"
#include "__fc_define_pthread_types.h"
#include "__fc_define_sa_family_t.h"
#include "__fc_define_seek_macros.h"
#include "__fc_define_sigset_t.h"
#include "__fc_define_size_t.h"
#include "__fc_define_sockaddr.h"
#include "__fc_define_ssize_t.h"
#include "__fc_define_stat.h"
#include "__fc_define_suseconds_t.h"
#include "__fc_define_time_t.h"
#include "__fc_define_timer_t.h"
#include "__fc_define_timespec.h"
#include "__fc_define_timeval.h"
#include "__fc_define_uid_and_gid.h"
#include "__fc_define_useconds_t.h"
#include "__fc_define_wchar_t.h"
#include "__fc_define_wint_t.h"
#include "__fc_gcc_builtins.h"
#include "__fc_inet.h"
#include "__fc_integer.h"
//#include "__fc_libc.h" //keep this; used by check_full_libc.sh
#include "__fc_machdep.h"
//#include "__fc_machdep_linux_shared.h" //keep this; used by check_full_libc.sh
#include "fcntl.h"
#include "__fc_select.h"
#include "__fc_string_axiomatic.h"
#include "features.h"
#include "fenv.h"
#include "float.h"
#include "fmtmsg.h"
#include "fnmatch.h"
#include "ftw.h"
#include "getopt.h"
#include "glob.h"
#include "grp.h"
#include "iconv.h"
#include "ifaddrs.h"
#include "inttypes.h"
#include "iso646.h"
#include "langinfo.h"
#include "libgen.h"
#include "limits.h"
#include "locale.h"
#include "malloc.h"
#include "math.h"
#include "memory.h"
#include "monetary.h"
#include "mqueue.h"
#include "ndbm.h"
#include "netdb.h"
#include "net/if.h"
#include "netinet/in.h"
#include "netinet/ip.h"
#include "netinet/tcp.h"
#include "nl_types.h"
#include "poll.h"
#include "pthread.h"
#include "pwd.h"
#include "regex.h"
#include "resolv.h"
#include "sched.h"
#include "search.h"
#include "semaphore.h"
#include "setjmp.h"
#include "signal.h"
#include "spawn.h"
#include "stdalign.h"
#include "stdarg.h"
#include "stdatomic.h"
#include "stdbool.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "stdnoreturn.h"
#include "string.h"
#include "strings.h"
#include "stropts.h"
#include "sys/file.h"
#include "sys/ioctl.h"
#include "sys/ipc.h"
#include "syslog.h"
#include "sys/mman.h"
#include "sys/msg.h"
#include "sys/param.h"
#include "sys/random.h"
#include "sys/resource.h"
#include "sys/select.h"
#include "sys/sendfile.h"
#include "sys/sem.h"
#include "sys/shm.h"
#include "sys/signal.h"
#include "sys/socket.h"
#include "sys/stat.h"
#include "sys/statvfs.h"
#include "sys/time.h"
#include "sys/times.h"
#include "sys/timex.h"
#include "sys/types.h"
#include "sys/uio.h"
#include "sys/un.h"
#include "sys/utsname.h"
#include "sys/vfs.h"
#include "sys/wait.h"
#include "tar.h"
#include "termios.h"
#include "tgmath.h"
#include "time.h"
#include "trace.h"
#include "ulimit.h"
#include "unistd.h"
#include "utime.h"
#include "utmp.h"
#include "utmpx.h"
#include "wait.h"
#include "wchar.h"
#include "wctype.h"
#include "wordexp.h"












void main() {
  /* The variables below must be const; otherwise the preconditions
     and the assigns/from of some functions will not match */
  //@ assert __fc_p_fopen == (FILE *)&__fc_fopen;
  //@ assert __fc_p_opendir == (DIR*)&__fc_opendir;
  //@ assert __fc_p_time_tm == &__fc_time_tm;
  //@ assert __fc_p_strerror == __fc_strerror;
}
