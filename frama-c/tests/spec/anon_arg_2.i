/* run.config*
STDOPT: #"%{dep:@PTEST_DIR@/anon_arg_1.i} @PTEST_FILE@"
*/

/*@ requires \valid(p);
    assigns *p \from x;
    ensures \result == x && *p == x;
*/
int f(int* p, int x);

/*@ requires \valid(p);
    assigns *p;
    ensures *p == \result;
*/
int g(int*p, int);
