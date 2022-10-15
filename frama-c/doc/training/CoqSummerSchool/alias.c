int y;
int* yptr = &y;
*yptr = 3;
/*@ assert y == 3; */
