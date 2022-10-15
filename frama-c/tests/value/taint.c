/* run.config*
   STDOPT: +" -eva-domains taint -eva-msg-key=d-taint,-d-cvalue -eva-auto-loop-unroll 10"
*/

#include <__fc_builtin.h>

volatile int undet;
int tainted;

void taint_basic(int t) {
  int u, w, x, y = 0;
  int buf[2] = { 0, 1 };

  /* Basic direct dependency: since 't' is tainted, 'x' becomes (data-)tainted. */
  x = t + y + 1;

  /* Data-dependency overapprox: since 'u' may take 't' in else-branch, then 'u'
     becomes (data-)tainted. */
  if (undet)
    u = 1;
  else
    u = t;

  /* Basic control-dependency: since 't' is tainted, 'w' becomes
     (control-)tainted no matter what. */
  if (t > 1)
    w = 1;
  else
    w = 2;

  /* Indirect dependency: since 't' is tainted, 'buf[t]' becomes
     (control-)tainted. */
  buf[t] = buf[1] + 1;

  Frama_C_dump_each();
}

void taint_assume_1() {
  int x, y, z;

  x = y = z = 0;
  /* 'x' becomes (data-)tainted at the end of first iteration, so the first two
     call to Frama_C_dump_each must report no taint. On second iteration, the
     first call to Frama_C_dump_each must report only 'x' as (data-)tainted,
     while the second call must report 'y' as (control-)tainted only as
     control-tainted only values do not impact data-tainteness. On the third
     iteration, the two calls must report both 'x' and 'y' as
     control-tainted. */
  while (x < 3) {
    Frama_C_dump_each();
    if (y % 2 == 0) {
      y += 2;
      Frama_C_dump_each();
    }
    //@ taint x;
    x++;
  }

  if (!z)
    /* Although 'z' does not post-dominate the 'x < 3', this latter is no more
       active here, hence 'z' remains untainted. */
    z++;
  Frama_C_dump_each();
}

void taint_assume_2() {
  int x, y = 0;
  /* As 'x' becomes (data-)tainted at some point, it will make 'y' tainted via a
     control-dependency. At the end, both must be control-tainted, but only 'x'
     is data-tainted. */
  for (x = 0; x < 8 || y <= 9; x++) {
    //@ split x;
    if (x == 5) {
      //@ taint x;
      x++;
    }
    y++;
  }
  Frama_C_dump_each();
}

void taint_undet_locs() {
  int x, y, t = 0;
  int *p = undet ? &x : &y;
  //@ taint t;
  x = t;
  y = t;
  /* Since 'p' may point to either 'x' or 'y', this assignment does not untaint
     'x' nor 'y' (which must both remain data-tainted). */
  *p = 0;
  Frama_C_dump_each();
}

/*@ assigns *l \from t; */
void taint_spec_assigns(int* l, int t);

void taint_goto_1() {
  int x, y, z, t;
  t = undet;
  //@ taint t;
  if (t > 0) {
    x = 1;
    goto L;
  }
  else {
    /* Since this assign is always executed, 'y' must not be tainted. */
    L: y = 0;
  }
  z = 1;
  Frama_C_dump_each();
}

void taint_goto_2() {
  int x, y, z, t;
  x = undet;
  t = undet;
  //@ taint t;
  if (x > 0) {
    if (t < 100) {
      x = 1;
      goto L;
    }
    /* As 'x' is untainted here, 'z' must remain untainted. */
    z = 1;
  }
  return;
  /* Since this assign may be executed depending on the condition on 't', which
     is tainted, 'y' must be (control-)tainted. */
  L: y = 0;
  Frama_C_dump_each();
}

void taint_call(int t) {
  int x = 0;
  if (t >= 0) {
    /* This call depends on the tainted 't', hence all left-values appearing in
       taint_basic must be control-tainted. */
    taint_basic(x);
  }
  /* 'x' must remain untainted here. */
  Frama_C_dump_each();
}

void taint_infinite_while(int t) {
  int i, w, x, y;
  if (!t)
    while (1) ;
  else {
    y = t + 1;
    /* Even though 't' is tainted and the assume is active on 'x', 'x'
       postdominates 't' because this is the only terminating path in this
       function: hence, 'x' must remain untainted. */
    x = 2;
  }
  if (t%2) {
    i = 0;
    while (++i) ;
  }
  else {
    /* However, the postdominators computation used by the domain is syntactic,
       so here 'w' is imprecisely (control-)tainted, even though this is the
       only terminating path of the function according to Eva. */
    w = 3;
  }
  Frama_C_dump_each();
}

void taint_struct(){
	struct Test{
		int x;
		int y;
	}test;
	struct Test test2;
	//@ taint test2;
	test = test2;
	Frama_C_dump_each();
}

// Taints global variable 'tainted'.
void taints (void) {
  tainted = Frama_C_interval(0, 10);
  //@ taint tainted;
}

int main(void) {
  /*taints();
  taint_basic(tainted);

  tainted = 0;
  taint_assume_1();
  taint_assume_2();

  taint_undet_locs();

  int l;
  taints();
  taint_spec_assigns(&l, tainted);
  //Here 'l' must be tainted
  Frama_C_domain_show_each(l);

  tainted = l = 0;
  taint_goto_1();
  taint_goto_2();*/

  taints();
  taint_call(tainted);

  //taints();
  //taint_infinite_while(tainted);
  
  //taints();
  //taint_struct();

  return 0;
}
