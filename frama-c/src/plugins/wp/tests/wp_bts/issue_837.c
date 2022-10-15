#define TEST(x) ( x ? 1 : 0 )

//@ assigns \nothing;
void foo(int a, int b)
{
  if (a && TEST(b)) ; else if (TEST(b))
    {} // BUG: the assigns is not proved by WP 
}

//@ assigns \nothing;
void bar(int a, int b)
{
  if (a && TEST(b)) ; else if (TEST(b))
    ; // OK: the assigns is correctly proved by WP
}
