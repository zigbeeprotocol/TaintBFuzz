/* run.config*
DONTRUN: main test in anon_arg_2.i
*/

int f(int*, int);

/*@ ensures \result == x; */
int g(int*, int x);
