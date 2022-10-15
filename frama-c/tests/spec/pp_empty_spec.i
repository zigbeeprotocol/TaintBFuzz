/* run.config
   MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
 */
int main(void) {
    int x = 0;
    int y = 0;
    /*@ loop invariant invmerger: chekofv_invariant_1_1: x==y; */
    while (y < 10) {
        x++;
        if (x!=9) y++;
    }
    return 0;
}
