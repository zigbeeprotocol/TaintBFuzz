volatile int a_rw,b_rw ;
volatile const int c_ro,d_ro ;

int rd(volatile int *p);
int rd_const(volatile const int *p);

int wr(volatile int *p,int v);
int wr_const(volatile const int *p,int v);

//@ volatile a_rw reads rd ;         // OK
//@ volatile b_rw reads rd_const ;   // OK
//@ volatile c_ro reads rd_const ;   // OK
//@ volatile d_ro reads rd ;         // OK

//@ volatile a_rw writes wr ;        // OK
//@ volatile b_rw writes wr_const ;  // KO
//@ volatile c_ro writes wr_const ;  // KO
//@ volatile d_ro writes wr ;        // KO
