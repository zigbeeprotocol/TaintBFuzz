/* run.config
   DONTRUN: main test is in ast_diff_1.i
*/
int X;
int Y=4;

int f(int x) {
  if (x <= 0)
    X = 0;
  else
    X = x;
  return X;
}

/*@ requires Y > 0;
    ensures X > 0;
    assigns X;
*/
int g() {
  X = Y;
  return X;
}

/*@ requires X > 0;
    ensures X > 0;
    assigns X;
*/
int h() {
  if (Y > 0)
    X = Y;
  return Y;
}

/*@ requires \is_finite(x);
    requires \is_finite(y);
    assigns \nothing;
    ensures \true != \false;
*/
int use_logic_builtin(double x, float y);

int has_static_local(void) {
  static int y = 0;
  y++;
  return y;
}

int used_in_decl;

/*@ exits \exit_status == 1; */
int decl() {
  used_in_decl++;
  return used_in_decl;
}

extern void i(void);

void (*ptr_func)(void) = &i;

/*@ type nat = Zero | Succ(nat); */

/*@ logic nat succ(nat n) = Succ(n); */

/*@ ensures succ(Zero) == Succ(Zero); */
extern void i(void);

void local_var_use(int w, int q[][w]) {
  int z;
  int t [sizeof(z)];
}

extern struct s s;

enum e;

struct s* use_s() { enum e* x; return &s; }

void with_goto_changed(int c) {
  if (c) goto L2;
  X++;
  L1: X++;
  L2: X++;
}

void with_goto_unchanged(int c) {
  if (c) goto L1;
  X++;
  L1: X++;
  L2: X++;
}
