/* run.config*
 EXIT: 0
   STDOPT:
*/


int a, b, c, d, e;

// Reminder: assigns are visited in reverse

/*@ assigns a;
    assigns a \from a, a, b, c, c; // more precise so replace the next one
    assigns a \from c, b, d, e, a;
    assigns a;
    assigns b \from a, e, b, d, c; // is ignored because the next one is more precise
    assigns b \from a, e;
    assigns c \from c, c, c, c, c; // both are kept (no inclusion)
    assigns c \from d;
 */
void function(void)
{
  return;
}
