/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

/*@ assigns \nothing;
    ensures \let count = d ; \result ==count;
*/
int op(int d) ;
int x,y;
void main () {
  x = op(33);
  y = op(31) ;
}
