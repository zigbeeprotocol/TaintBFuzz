typedef volatile unsigned Vunsigned;

unsigned g(Vunsigned * q);
unsigned f(volatile unsigned * q);

volatile unsigned *p = (volatile unsigned *)(0x4);
//@ volatile *p reads g;
//@ volatile *((Vunsigned *)(0x4)) reads f;
//@ volatile *((unsigned volatile *)(0x6)) reads f;

Vunsigned f1(Vunsigned * q);
Vunsigned g1(volatile unsigned * q);
volatile unsigned *pf1, *pg1, *pg;
//@ volatile *pg  reads g;
//@ volatile *pf1 reads f1;
//@ volatile *pg1 reads g1;

typedef const int Cint ;
volatile Cint ci1, ci2, ci3, ci4;

Cint rd_ci1 (Cint volatile *p) ;
Cint rd_ci2 (const int volatile *p) ;
int  rd_ci3 (Cint volatile *p) ;
int  rd_ci4 (const int volatile *p) ;

//@ volatile ci1 reads rd_ci1;
//@ volatile ci2 reads rd_ci2;
//@ volatile ci3 reads rd_ci3;
//@ volatile ci4 reads rd_ci4;

typedef enum { e=-1} Enum;
volatile Enum e3;
Enum  wr_e3 (Enum volatile *p, const Enum v) ;

//@ volatile e3 writes wr_e3;

Enum fe(Enum a);
void ge(void) {
  e3 = fe(e3);
}

typedef const Enum CEnum ;
volatile CEnum ce1, ce2, ce3, ce4;

CEnum wr_ce1 (CEnum volatile *p, const Enum v) ;
CEnum wr_ce2 (const Enum volatile *p, const Enum v) ;
Enum  wr_ce3 (CEnum volatile *p, const Enum v) ;
Enum  wr_ce4 (const Enum volatile *p, const Enum v) ;
