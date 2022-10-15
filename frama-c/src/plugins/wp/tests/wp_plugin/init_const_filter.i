int const GlobalConst[16];

/*@ requires 0 ≤ ClientId < 16; */
void default_init(char const ClientId)
{
  int R1;
  R1 = GlobalConst[ClientId];
	//@ check X: GlobalConst[ClientId] == R1 == 0 ;
}
