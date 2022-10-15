#include <string.h>

/*@ assigns dest[0..strlen{Old}(src)];  @*/
void strcpy_OLD(char *restrict dest, const char *restrict src);

/*@
	requires \separated(dest+(0..), src+(0..));
	assigns dest[0..strlen(src)];
*/
void old(char *dest, const char *src) {
    strcpy_OLD(dest, src);
}
