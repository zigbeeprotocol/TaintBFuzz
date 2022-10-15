/*@ type t; */
/*@ logic t create(int x); */
/*@ logic t1 create(int y); // error: type does not exist
*/

/*@ type t2 = t2; */
//@ logic t2 foo;
//@ predicate p(t2 x) = foo == x;

typedef struct { int x ; int y ; } Point ;
/*@ axiomatic A {
    type point = Point;
    predicate Q(point * tt) reads tt[0..1], tt[2].x, tt[2].y;
    type triangle = point[3];
    predicate P(triangle tt) = tt[1].x == tt[2].y;
    } */

/*@ ensures Q(q);
  @ ensures P((triangle) q); */
void f(Point *q);

Point tab[3];

/*@ ensures Q(&tab[0]);
  @ ensures P(tab); */
void h(void) {
  f(tab) ;
}

//@ logic t t_from_t(t x) = (t) x;

//@ logic _Bool _Bool_from_boolean(boolean b) = (_Bool) b;

//@ logic boolean boolean_from_integer(integer b) = (boolean) b;
//@ logic boolean boolean_from_int(int b) = (boolean) b;
//@ logic boolean boolean_from_Bool(_Bool b) = (boolean) b;

typedef struct INTEGER { int integer; } Integer ;
/*@ axiomatic B {
  logic integer value{L}(Integer *p) = p->integer;
} */

typedef struct COMPLEX { double real,img; } Complex ;
/*@ axiomatic CPX {
  type complex = Complex;
  logic double re{L}(complex *p) = p->real;
  logic complex with_re(complex c, double re) = { c \with .real = re };
} */

