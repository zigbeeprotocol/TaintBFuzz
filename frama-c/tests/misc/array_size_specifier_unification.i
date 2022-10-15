/* run.config
   OPT: -print -check
*/

extern int t[3U];
int t[2+1];
int t[4/4 + 2];

extern int c[2147483648];
int c[2147483647+1U];

extern int u[5+5];
int u[5LL+5];

int main(void){ return 0; }
