int x, y;
struct st {
  char  c;
  short i;
  int  *p, *t[2];
} v = { 1, 2, &x, &y};

struct st approx (int c0) {
  struct st r;
  int *q1, *q2;
  
  r.c = lib_fct() ; 
  r.i = c0 ; 
  r.p = *(int *) (&v.c + 3); 
  q1 =           *(int**)(2 + (char *) v.t);
  q2 = c0 ? q1 : *(int**)(3 + (char *) v.t);
  r.t[0] = q2 ;
  r.t[1] = (int *)(- (int)&x) ;
  return r;
}
