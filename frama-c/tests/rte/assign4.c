/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

//@ assigns \result \from min, max;
int choose1(int min, int max);

/*@ assigns \result \from min, max, min, max;
  assigns \result \from min, max, min, max; */
int choose2(int min, int max);

int main() {
  int c1 = choose1(5,10);
  int c2 = choose2(0,c1);
  return c1+c2;
}
