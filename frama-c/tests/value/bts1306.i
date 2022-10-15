/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -constfold -eva-slevel 0 -eva @EVA_CONFIG@ -print -then -eva-slevel 10 -eva -print
   */

void g(double x) { double y= x*x; }

int main(double x)
{
    g(x);
    return 0;
}
