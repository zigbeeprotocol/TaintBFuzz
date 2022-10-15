/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -eva @EVA_CONFIG@ -then -eva-initialization-padding-globals maybe
*/
int t[5] = { [2] = 3 };

struct { char a; int t[5]; } s = { 'a' , { [2] = 3 } };

int u[6] = { [4] = 4, [2] = 2 };

void main(void)
{
}
