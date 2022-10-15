/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -eva @EVA_CONFIG@ -eva-slevel 30 -float-normal
*/

int sq,s;

float rq,r;

void main(int c)
{
  s = (c >= -10) ? ((c <= 10) ? c : 0) : 0;
  r = s;
  //@ assert s >= 0 || s < 0 ;
  sq = s * s;

  //@ assert r >= 0.0 || r < 0.0 ;
  rq = r * r;
}
