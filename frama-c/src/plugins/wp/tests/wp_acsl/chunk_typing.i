/* run.config
   OPT: -wp-rte
*/
/* run.config_qualif
   OPT: -wp-rte
*/

const char x[10];

/*@
  requires \valid(&i8[0..9])  && \valid(&u8[0..9])  && \valid(&i16[0..9])
        && \valid(&u16[0..9]) && \valid(&i32[0..9]) && \valid(&u32[0..9])
        && \valid(&i64[0..9]) && \valid(&u64[0..9]);
  ensures
    \forall integer k ; 0 <= k < 10 ==> x[k]+8
                                     == i8[k]+7  == u8[k]+6
                                     == i16[k]+5 == u16[k]+4
                                     == i32[k]+3 == u32[k]+2
                                     == i64[k]+1 == u64[k];
*/
void function(signed char i8[10],
              unsigned char u8[10],
              signed short i16[10],
              unsigned short u16[10],
              signed int i32[10],
              unsigned int u32[10],
              signed long long int i64[10],
              unsigned long long int u64[10])
{
  /*@
    loop invariant 0 <= i <= 10;
    loop invariant \forall integer k ; 0 <= k < i ==> i8[k] == 1 ;
    loop invariant \forall integer k ; 0 <= k < i ==> u8[k] == 2 ;
    loop invariant \forall integer k ; 0 <= k < i ==> i16[k] == 3 ;
    loop invariant \forall integer k ; 0 <= k < i ==> u16[k] == 4 ;
    loop invariant \forall integer k ; 0 <= k < i ==> i32[k] == 5 ;
    loop invariant \forall integer k ; 0 <= k < i ==> u32[k] == 6 ;
    loop invariant \forall integer k ; 0 <= k < i ==> i64[k] == 7 ;
    loop invariant \forall integer k ; 0 <= k < i ==> u64[k] == 8 ;
    loop assigns i, i8[0..9], u8[0..9], i16[0..9], u16[0..9],
                    i32[0..9], u32[0..9], i64[0..9], u64[0..9] ;
    loop variant 10-i;
  */
  for (int i = 0; i < 10; ++i) {
    i8[i] = 1;
    u8[i] = 2;
    i16[i] = 3;
    u16[i] = 4;
    i32[i] = 5;
    u32[i] = 6;
    i64[i] = 7;
    u64[i] = 8;
  }
}
