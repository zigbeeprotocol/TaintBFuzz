/* run.config
   STDOPT: +"%{dep:@PTEST_DIR@/merge_bts0948_1.i}" +"%{dep:@PTEST_DIR@/merge_bts0948_2.i}"
*/

/*@ requires \valid((char*)dest);
*/
extern void *memcpy(void * dest);

void* memcpy(void* region1) { return region1; }
