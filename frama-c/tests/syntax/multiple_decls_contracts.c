/* run.config
OPT: @FRAMAC_SHARE@/libc/string.h @PTEST_FILE@ @PTEST_FILE@ -cpp-extra-args="-I@FRAMAC_SHARE@/libc" -print
OPT: @PTEST_FILE@ @FRAMAC_SHARE@/libc/string.h @PTEST_FILE@ -cpp-extra-args="-I@FRAMAC_SHARE@/libc" -print
OPT: @PTEST_FILE@ @PTEST_FILE@ @FRAMAC_SHARE@/libc/string.h -cpp-extra-args="-I@FRAMAC_SHARE@/libc" -print
*/

#include "string.h"
#include "stdlib.h"

char *
strdup(const char *str)
{
    if (str != NULL) {
        register char *copy = malloc(strlen(str) + 1);
        if (copy != NULL)
            return strcpy(copy, str);
    }
    return NULL;
}
