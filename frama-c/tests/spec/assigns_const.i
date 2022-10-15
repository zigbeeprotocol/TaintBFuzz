int i ;
int const c ;

//@ assigns i ;
void accept_non_const(void);

//@ assigns c ;
void refuse_const(void);

const int a[2];

//@ assigns a[0] ;
void refuse_const_array(void);

//@ assigns { i, c };
void refuse_const_in_set(void);

struct X { int const f; };
struct Y { struct X a[10] ; };
struct Y y ;

//@ assigns y.a[4].f ;
void refuse_const_field(void);

//@ assigns (*ptr).a[4].f ;
void refuse_field_via_pointer(struct Y * ptr);

// Acceptable const assigns:

//@ assigns *ptr ;
void accept_const_via_pointer(int const * ptr);

struct Z {
  const int x;
  int y;
};

static struct Z z;

//@ assigns z.y;
void accept_partial_const_struct(void)
{
    z.y = 1;
}

struct T {
  const struct Z z ;
};
struct T t ;


//@ assigns t.z.y ; // y is not const but z is
void refuse_const_path(void){

}
