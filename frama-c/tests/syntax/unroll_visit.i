/* run.config
PLUGIN: eva,scope,from,inout
   STDOPT: +"-eva @EVA_CONFIG@ -deps -out -input -deps"
 */

typedef char i8; // ideally, pretty-printing should keep 'i8' for some casts

void main() {
   /*@ loop pragma UNROLL 2; */
  for(i8 i=0; i<100; i++) {
    i--;
    //@ assert i<100;
    i++;
  }
}
