/* run.config
   CMD: @frama-c@ -wp -wp-msg-key shell,cluster,print-generated -wp-prover why3 -wp-gen -wp-share @PTEST_SHARE_DIR@ -wp-warn-key "pedantic-assigns=inactive"
   OPT:
*/

/* run.config_qualif
   DONTRUN:
*/

struct FD {
  int pos;
  int *adr;
};

struct A { int dummy; };

/*@
  assigns fd->pos;
  assigns *a;
  ensures fd->pos != \old(fd->pos);
*/
int myRead(struct FD* fd,struct A* a);

/*@
  ensures KO: *a == \old(*a);
*/
void myMain(struct FD* fd,struct A* a)
{
  myRead(fd,a);
}
