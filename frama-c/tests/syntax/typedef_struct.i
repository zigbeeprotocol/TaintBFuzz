/* run.config
OPT: %{dep:typedef_struct_2.i} @PTEST_FILE@ %{dep:typedef_struct_2.i} -print
*/
typedef struct foo foo;
extern foo *alloc(void);

foo* f(int x);

struct foo
{
    int y;
};

foo* f(int x)
{
    foo* f = alloc();
    if (f->y == x) return 0;
    return f;
    }
