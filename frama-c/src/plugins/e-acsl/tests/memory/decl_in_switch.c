/* run.config
   COMMENT: Check that variables declared in the body of switch statements are
   correctly tracked.
*/

/// Simple declaration in switch
void decl_in_switch(int value) {
  switch (value) {
    int *p;
  default: {
    p = &value;
    /*! assert \valid(p); */
    break;
  }
  }
}

/// Declaration and initialization in a single statement
/// (local initializer)
void compound_decl_and_init(int value) {
  int a = 0;
  /*@ assert \valid(&a); */

  switch (value) {
    int b = 2;
    /*@ assert \valid(&b); */

  case 0:;
    int c = 3;
    /*@ assert \valid(&c); */
    break;

  case 1:;
    int d = 4;
    /*@ assert \valid(&d); */
    break;
  }
}

/// Separate statements for declaration and initialization
/// (no local initializer)
void separate_decl_and_init(int value) {
  int a;
  a = 1;
  /*@ assert \valid(&a); */

  switch (value) {
    int b;
    b = 2;
    /*@ assert \valid(&b); */

  case 0:;
    int c;
    c = 3;
    /*@ assert \valid(&c); */
    break;

  case 1:;
    int d;
    d = 4;
    /*@ assert \valid(&d); */
    break;
  }
}

/// Check label in switch
void label_in_switch(int value) {
  int done = 0;

  switch (value) {
  /* standalone label */
  K:;
    int d = 0;
    /*@ assert \valid(&d); */

  /* Label and case on the same statement */
  L:
  case 0:;
    int e = 1;
    /*@ assert \valid(&e); */
    break;
  case 1:;
    int ff = 2;
    /*@ assert \valid(&ff); */
    break;
  }

  if (!done) {
    done = 1;
    if (value < 10) {
      goto L;
    } else {
      goto K;
    }
  }
}

int main(int argc, char **argv) {
  decl_in_switch(argc);
  compound_decl_and_init(argc);
  separate_decl_and_init(argc);
  label_in_switch(argc);
  return 0;
}
