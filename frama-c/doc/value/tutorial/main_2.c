#include "skein.h"
#include "__fc_builtin.h"

#define HASHLEN (8)

u08b_t msg[80];

int Frama_C_interval(int,int);

void main(void)
{
  int i;
  u08b_t hash[HASHLEN];
  Skein_256_Ctxt_t skein_context; 

  for (i=0; i<80; i++) msg[i]=Frama_C_interval(0, 255);

  Skein_256_Init( &skein_context, HASHLEN * 8);
  Skein_256_Update( &skein_context, msg, 80);
  Skein_256_Final( &skein_context, hash);
}
