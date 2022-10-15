/*@
  requires \initialized(buf + (0 .. count - 1));
*/
int test(char *buf, int count);

// Success:

void succ_full_first_cell(void){
  char buf[3] = {0};
  test(buf    , 1);
}
void succ_full_full(void){
  char buf[3] = {0};
	test(&buf[0], 3);
}
void succ_full_from_1(void){
  char buf[3] = {0};
	test(buf+1  , 2);
}
void succ_from_1_from_1(void){
  char buf[3];
	buf[1] = buf[2] = 1 ;
	test(buf+1  , 2);
}
void succ_full_from_2(void){
  char buf[3] = {0};
	test(&buf[2], 1);
}

// Failure:

void fail_cell_before(void){
  char buf[3] = {0};
	test(buf-1  , 1);
}
void fail_too_long(void){
  char buf[3] = {0};
	test(buf    , 4);
}
void fail_too_long_from_1(void){
  char buf[3] = {0};
	test(&buf[1], 3);
}
void fail_too_long_from_2(void){
  char buf[3] = {0};
  test(buf+2  , 2);
}
void fail_cell_after_end(void){
  char buf[3] = {0};
	test(buf+3  , 1);
}
void fail_partial_not_full(void){
  char buf[3];
	buf[0] = buf[1] = 0;
	test(&buf[0], 3);
}
