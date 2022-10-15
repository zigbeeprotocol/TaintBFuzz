#include "skein.h"
#include <stdio.h>

#define HASHLEN (8)

u08b_t msg[80]="People of Earth, your attention, please";

int main(void)
{
  u08b_t hash[HASHLEN];
  int i;
  Skein_256_Ctxt_t skein_context;
  Skein_256_Init( &skein_context, HASHLEN);
  Skein_256_Update( &skein_context, msg, 80);
  Skein_256_Final( &skein_context, hash);
  for (i=0; i<HASHLEN; i++)
    printf("%d\n", hash[i]);
  return 0;
}
