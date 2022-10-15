/*@ axiomatic Ax { predicate Kept reads \nothing ; } */

/*@ ensures Kept && \result == \null ; */
char *m(void);

void foo() {
	char** pages = (void*)0;
	pages = m();
	/*@ assert MUST_FAIL: pages == \null ; */
}
