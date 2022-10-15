/* run.config
   STDOPT:
   STDOPT: #"-warn-signed-downcast "
 */

int main(void) {
  signed char cx, cy, cz;

  cz = cx + cy;
  return 0;
}
