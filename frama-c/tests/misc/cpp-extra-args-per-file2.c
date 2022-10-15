/* run.config
   DONTRUN: main test is cpp-extra-args-per-file1.c
 */

#ifndef GLOBAL
#error GLOBAL must be defined
#endif

#ifndef FILE2
#error FILE2 must be defined
#endif

#ifdef FILE1
#error FILE1 must NOT be defined
#endif
