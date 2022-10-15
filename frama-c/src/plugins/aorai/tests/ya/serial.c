/* run.config
  OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-smoke-tests -aorai-test-number @PTEST_NUMBER@ -aorai-no-acceptance -aorai-instrumentation-history 2 -aorai-no-generate-annotations -aorai-no-generate-deterministic-lemmas -then-last -eva -eva-partition-value n -eva-ilevel 256
*/
/* run.config_prove
OPT: -cpp-extra-args="-DFOR_WP" -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@_wp.ya}  -aorai-smoke-tests -aorai-test-number @PTEST_NUMBER@ -aorai-no-acceptance @PROVE_OPTIONS@
*/

#include "__fc_builtin.h"

#ifndef FOR_WP
#define BW_AND &
#define BW_AND2 &
#define BW_AND3 &
#else
#define BW_AND ==
#define BW_AND2 >=
#define BW_AND3 <=
#endif

/*@ assigns \result,Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures 0 <= \result < 0x100; */
int input_status(void) {
  return Frama_C_interval(0x00, 0xff);
}

/*@ assigns \result,Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures 0 <= \result < 0x100; */
int input_data(void) {
  return Frama_C_interval(0x00, 0xff);
}

/*@ assigns \nothing; */
void output(int x, int y) {
  // do nothing
}


int read(int *status)
{
  int s = input_status();

  if (s BW_AND2 0x01) {
    *status = s BW_AND 0x0e;
    return input_data();
  }

  return -1;
}


volatile int indefinitely;

int buffer[5]; // buffer to store bytes
int n = 0; // number of bytes received

void main(void)
{
  while (indefinitely)
  {
    int status;
    int data = read(&status);

    if (data != -1) { // data is present

      if (status != 0) { // read issue
        n = 0;
        continue;
      }
      if (data BW_AND3 0x80) { // status received
        if (n != 0) { // but data was expected
          n = 0;
          continue;
        }
        //@ split data & 0x40;
      }
      else { // data receieved
        if (n == 0) { // but status was expected}
          continue;
        }
      }

      buffer[n++] = data;

      if (n == 5) { // the packet is completely read
        if ((buffer[0] BW_AND 0x40) == 0) // it is a release action
        {
          int x = buffer[1] + 0x80 * buffer[2];
          int y = buffer[3] + 0x80 * buffer[4];
          output(x, y);
          /* "Error" state should show up as, for now, it is  hard to prove
            the metavariable équation in the input automaton */
          Frama_C_show_aorai_state(n,x,y);
        }

        n = 0;
      }
    }
  }
}
