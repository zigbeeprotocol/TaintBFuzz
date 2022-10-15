/* run.config*
OPT: -print
*/
// announce that we are a non-conforming C++ compiler
#define __cplusplus 1L
#include <stdbool.h>
#ifdef bool
#error bool should not be defined in C++ mode
#endif
#ifdef true
#error true should not be defined in C++ mode
#endif
#ifdef false
#error false should not be defined in C++ mode
#endif
int main() { return 0; }
