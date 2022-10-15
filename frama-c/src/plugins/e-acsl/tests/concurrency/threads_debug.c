/* run.config, run.config_dev
  COMMENT: This test is identical to `parallel_thread.c` but with RTL debug code
  COMMENT: activated.
  MACRO: ROOT_EACSL_GCC_OPTS_EXT --rt-debug --rt-verbose --concurrency

  COMMENT: Filter the addresses of the output so that the test is deterministic.
  MACRO: ROOT_EACSL_EXEC_FILTER sed -e s_0x[0-9a-f-]*_0x0000-0000-0000_g | sed -e s_Offset:\s[0-9-]*_Offset:xxxxx_g | sed -e s/[0-9]*\skB/xxxkB/g | sed -e s/[0-9]*\sMB/xxxMB/g | sed -e s/Leaked.*bytes/Leakedxxxbytes/g
*/

// Include existing test
#include "parallel_threads.c"
