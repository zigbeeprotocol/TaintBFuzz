/* run.config*
 PLUGIN: @EVA_PLUGINS@ report
   OPT: @EVA_OPTIONS@ -print -eva -report
 MODULE: big_local_array_script
   OPT: @EVA_OPTIONS@ -then-on prj -print -report
 PLUGIN: @EVA_PLUGINS@
 MODULE:
   OPT: @EVA_OPTIONS@ -print -no-initialized-padding-locals -eva
*/

struct S {
  int a[50];
  int b[32];
};

int main () {
  struct S x[32] =
    { [0] = { .a = { 1,2,3 }, .b = { [5] = 5, 6, 7 }},
      [3] = { 0,1,2,3,.b = { [17]=17 } }
    };
}
