/* run.config*
 EXIT: 1
   STDOPT:
*/


int f(int t[-1]) { return t[0]; } // should raise an error
