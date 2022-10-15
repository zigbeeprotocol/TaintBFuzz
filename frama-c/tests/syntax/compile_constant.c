#define M0(x) (x)*(x)<4.0?0.0:1.0
char pixels[] = {M0(0.0), M0(1), M0(2.0f)};

/* tests below should evaluate to 2. */

char test_neg = { (-0.) ? 1. : 2. };

char test_ge = { ((-1.) >= 0.) ? 1. : 2. };

char test_cast[] = { 1 >= (0?1U:(-1)) ? 1. : 2.,
                   ((double)1) >= (0?1U:(-1)) ? 1. : 2. };

double a = 2 >= 5 ? 5 ? (long)0 || 0 ? 0. >= 0 ?: 0 : 2 : 5 : 0;

extern int f(void);

/* no call should be evaluated. */
char no_call[] = { 1 ? 1 : f(), 0?f():2 };
