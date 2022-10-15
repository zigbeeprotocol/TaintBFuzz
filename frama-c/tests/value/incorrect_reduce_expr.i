/* run.config*
 PLUGIN: @EVA_MAIN_PLUGINS@
   OPT: -eva @EVA_CONFIG@ -absolute-valid-range 32-36
*/
char t[5];
int *p;
int x;
void main(int c)
{
  x = 13;
  p = (int*)32;
  if (c) p+=1;
  *(char*)p = 13;
}
  
  
