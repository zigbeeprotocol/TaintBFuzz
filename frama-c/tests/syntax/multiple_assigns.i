/* run.config*
 EXIT: 0
   STDOPT:
*/
int z;

/*@ assigns z, z;
    assigns z \from z;
    assigns z, z;
 */
void function(void)
{
  return;
}
