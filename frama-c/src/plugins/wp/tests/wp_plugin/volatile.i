/* run.config
   OPT:
   OPT: -wp-no-volatile
*/
/* run.config_qualif
   OPT:
   OPT: -wp-no-volatile
*/


volatile int v ;

void job_assigns(void)
{
  v = 0;
  /*@ assert KO_WHEN_VOLATILE: v == 0 ; */ ;
}

void job_read(void)
{
  int x = v;
  /*@ assert KO_WHEN_VOLATILE: x == v ; */ ;
}

struct st_v { int a ; int volatile v ; } sv;

void job_struct(void)
{
  sv.a = 0;
  if (sv.a) /*@ assert ok: dead_code: \false ; */ ;
}

void job_struct_assigns(struct st_v *p)
{
  *p = sv;
  /*@ assert KO_WHEN_VOLATILE: *p == sv ;  */ ;
}

int const volatile GlobalConst[16];

/*@ requires 0 ≤ ClientId < 16; */
void default_init(char const ClientId)
{
  int R1;
  R1 = GlobalConst[ClientId];
	//@ check KO_WHEN_VOLATILE: R1 == 0 ;
}
