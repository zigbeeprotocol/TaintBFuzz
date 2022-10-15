/** Label devant l'appel à la fonction variadique : il doit être
    conservé lorsqu'on remplace l'appel. */

int f(int, ...);

int main(){
 lbl:
  f(1, 2, 3);
  return 0;
}
