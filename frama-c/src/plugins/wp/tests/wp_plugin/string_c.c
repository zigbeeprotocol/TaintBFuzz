/* run.config
STDOPT: +"-wp-fct memcpy,memmove"
 */
/* run.config_qualif
STDOPT: +"-wp-fct memcpy,memmove -wp-steps 2500 -wp-timeout 120"
 */

#include "string.c"
/* That includes the C file of Frama-C Stdlib : FRAMA-C-ROOT/share/libc/string.c
   In such a file, some functions (i.e. memcpy) have no explicit specification but a generated one.
   Theses specifications may use generated logical functions (i.e. memcmp) and generated axioms.
*/
