/*@ predicate isMax( integer x, integer y, integer z ) = x < y ? x == z : y == z ; */

/*@ ensures isMax(a,b,\result); */
int getMax(int a,int b) { return a <= b ? a : b; }
