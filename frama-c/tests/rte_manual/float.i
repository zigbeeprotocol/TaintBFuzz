/* run.config
   STDOPT: #"-rte-float-to-int -warn-special-float none "
 */

int f(float v) {
  int i = (int)(v+3.0f);
  return i;
}
