/* run.config
 COMMENT: to uncomment with dune -> PLUGIN: @PTEST_PLUGIN@ markdown-report.eva-info
   OPT: -mdr-remarks %{dep:@PTEST_DIR@/@PTEST_NAME@.remarks.md}
 */

/* extracted from Juliet test suite v1.3 for C
   https://samate.nist.gov/SRD/view_testcase.php?tID=76270
*/

#include <stdlib.h>
#include <string.h>

void CWE126_Buffer_Overread__malloc_char_loop_64b_badSink(void * dataVoidPtr)
{
    /* cast void pointer to a pointer of the appropriate type */
    char * * dataPtr = (char * *)dataVoidPtr;
    /* dereference dataPtr into data */
    char * data = (*dataPtr);
    {
        size_t i, destLen;
        char dest[100];
        memset(dest, 'C', 100-1);
        dest[100-1] = '\0'; /* null terminate */
        destLen = strlen(dest);
        /* POTENTIAL FLAW: using length of the dest where data
         * could be smaller than dest causing buffer overread */
        for (i = 0; i < destLen; i++)
        {
            dest[i] = data[i];
        }
        dest[100-1] = '\0';
        free(data);
    }
}

void CWE126_Buffer_Overread__malloc_char_loop_64_bad()
{
    char * data;
    data = NULL;
    /* FLAW: Use a small buffer */
    data = (char *)malloc(50*sizeof(char));
    if (data == NULL) {exit(-1);}
    memset(data, 'A', 50-1); /* fill with 'A's */
    data[50-1] = '\0'; /* null terminate */
    CWE126_Buffer_Overread__malloc_char_loop_64b_badSink(&data);
}

/* goodG2B uses the GoodSource with the BadSink */
void CWE126_Buffer_Overread__malloc_char_loop_64b_goodG2BSink(void * dataVoidPtr)
{
    /* cast void pointer to a pointer of the appropriate type */
    char * * dataPtr = (char * *)dataVoidPtr;
    /* dereference dataPtr into data */
    char * data = (*dataPtr);
    {
        size_t i, destLen;
        char dest[100];
        memset(dest, 'C', 100-1);
        dest[100-1] = '\0'; /* null terminate */
        destLen = strlen(dest);
        /* POTENTIAL FLAW: using length of the dest where data
         * could be smaller than dest causing buffer overread */
        for (i = 0; i < destLen; i++)
        {
            dest[i] = data[i];
        }
        dest[100-1] = '\0';
        free(data);
    }
}

static void goodG2B()
{
    char * data;
    data = NULL;
    /* FIX: Use a large buffer */
    data = (char *)malloc(100*sizeof(char));
    if (data == NULL) {exit(-1);}
    memset(data, 'A', 100-1); /* fill with 'A's */
    data[100-1] = '\0'; /* null terminate */
    CWE126_Buffer_Overread__malloc_char_loop_64b_goodG2BSink(&data);
}

void CWE126_Buffer_Overread__malloc_char_loop_64_good()
{
    goodG2B();
}

int main(int argc, char * argv[])
{
    CWE126_Buffer_Overread__malloc_char_loop_64_good();
    CWE126_Buffer_Overread__malloc_char_loop_64_bad();
    return 0;
}

