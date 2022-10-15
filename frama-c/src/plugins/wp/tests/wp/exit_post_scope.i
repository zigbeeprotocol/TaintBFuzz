void bar(void);

/*@
  ensures \valid(&f);
  exits \valid(&f);
*/
void foo(int f){
  bar();
}
