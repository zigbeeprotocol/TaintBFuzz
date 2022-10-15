/* run.config
OPT:
EXIT:1
OPT: -cpp-extra-args="-DINVALID_ZERO_BF"
 */

struct foo
{
        unsigned        bar  : 16, : 0;
        unsigned        bla  : 11, : 1;
        unsigned        bli  : 4,  : 0;
};

#ifdef INVALID_ZERO_BF
struct invalid_foo
{
  unsigned        first  : 1;
  unsigned        zero_with_name: 0;
  unsigned        last  : 2;
};
#endif

unsigned f(struct foo s) { return s.bla; }
