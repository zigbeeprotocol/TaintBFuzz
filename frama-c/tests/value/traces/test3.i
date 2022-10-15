/* run.config
   STDOPT: #"-eva-domains traces -eva-msg-key d-traces -eva-slevel 10 -eva-traces-project" +"-then-last -eva -print -eva-msg-key=-d-traces"
*/

int g;

int main(int c){
  int tmp = 4;
  if(tmp){
    g = tmp;
  } else {
    g = 1;
  }
  return g+1;
}
