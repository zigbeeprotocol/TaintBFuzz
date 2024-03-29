/* run.config_qualif
   OPT: -wp -wp-par 1
*/

int t[20];

int mat[10][5];

struct S {int i; int tab[4];};

int x;

struct S s;
struct S ts[4];

/*@
   ensures Pt: \block_length(&t) == 20*sizeof(int) ;
   ensures Psiz1 : sizeof(mat[1]) == 5*sizeof(int);
   ensures Pmat1 : \block_length(&mat[1]) == 50*sizeof(int);
   ensures Psiz2 : sizeof(mat) == 50*sizeof(int);
   ensures Pmat2 : \block_length(&mat) == 50*sizeof(int);
   ensures Ps : \block_length(&s) == \block_length(&x) + 4*sizeof(int);
   ensures Pts : \block_length(&ts) == 4* \block_length(&s);

   ensures Pt1: \block_length(&t[1]) == 20*sizeof(int) ;
   ensures Pmat12 : \block_length(&mat[1][2]) == 50*sizeof(int);
   ensures Pts1 : \block_length(&ts[1]) == 4* \block_length(&s);
 */
void f(void){return;}

/*@ // FORCE EVERYTHING IN MEMTYPED
  requires pt == &t && pmat == &mat && px == &x && ps == &s && pts == &ts ;
  ensures Pt: \block_length(pt) == 20*sizeof(int) ;
  ensures Psiz1 : sizeof((*pmat)[1]) == 5*sizeof(int);
  ensures Pmat1 : \block_length(&(*pmat)[1]) == 50*sizeof(int);
  ensures Psiz2 : sizeof(*pmat) == 50*sizeof(int);
  ensures Pmat2 : \block_length(pmat) == 50*sizeof(int);
  ensures Ps : \block_length(ps) == \block_length(px) + 4*sizeof(int);
  ensures Pts : \block_length(pts) == 4* \block_length(ps);

  ensures Pt1: \block_length(&(*pt)[1]) == 20*sizeof(int) ;
  ensures Pmat12 : \block_length(&(*pmat)[1][2]) == 50*sizeof(int);
  ensures Pts1 : \block_length(&(*pts)[1]) == 4* \block_length(ps);
*/
void g(int (*pt)[20], int (*pmat)[10][5], int* px, struct S *ps, struct S (*pts)[4]){

}
