/* run.config_qualif
   OPT: -wp -wp-model Typed -wp-par 1 -wp-prop="-zbit"
*/

/*@ ensures \result == (int) (a & b & c); 
  @ ensures band0: 3!=(\result & 0xF0);
  @ behavior bit0:
  @   assumes bit0: 1==(a & 1) && 1==(b & 1) && 1==(c & 1);
  @   ensures band1: 1==(\result & 1);
  @   ensures band2: 0!=(\result & 1);
  @ behavior bit1:
  @   assumes bit1: 0==(b & 2);
  @   ensures band3: 0==(\result & 2);
  @ behavior bit2:
  @   assumes bit2: 0!=(c & 4);
  @   ensures band4: (\result & 4) == (a & b & 4);
  @ behavior bit3:
  @   assumes bit3: 2!=(a & 2) && 0==(b & c & 2) && 1 != (a & b & 1);
  @   ensures band5: (\result & 2) == (a & b & 1);
  @ behavior bit4: 
  @   assumes bit4: a==-1 && b==~0 && c==-1; 
  @   ensures band6: \result==-1;
  @ behavior bit5:
  @   ensures band7: zbit: (0x55==(0xFFF & a)) ==> (0x5555!=(0xFFFF & a));
 */
int band(int a,int b,int c) { return a & b & c; }

/*@ ensures \result == (int) (a | b | c); 
  @ ensures bor0: 3!=(\result | 0xF0);
  @ behavior bit1:
  @   assumes bit1: 2==(a & 2);
  @   ensures bor1: 2==(\result & 2);
  @ behavior bit2:
  @   assumes bit2: 0==(a & 4) && 0==((b | c) & 4);
  @   ensures bor2: 0==(\result & 4);
  @ behavior bit3: 
  @   assumes bit3: a==0 && b == 0 && c==0; 
  @   ensures bor3: \result==0;
 */
int bor(int a,int b, int c) { return a | b | c ; }

/*@ ensures \result == (int) (a ^ b);
  @ behavior bit1:
  @   assumes a == -1 && 0xFF==(0xF0^b);
  @   ensures \result == ~0x0F;
  @ behavior bit2:
  @   assumes a == b;
  @   ensures \result == 0;
  @ behavior bit3:
  @   assumes a == ~b;
  @   ensures \result == -1;
 */ 
int bxor(int a,int b) { return a ^ b ; }

//@ ensures \result == (int) (~a) ;
int bnot(int a) { return ~a ; }

/*@ ensures \result == (int) (a << n) ;
  @  behavior shift1:
  @    assumes n == 3;
  @    ensures lsl1: ((a & 1) != 0) == (0 != (\result & 8));
  @    ensures lsl2: 1 != (\result & 1);
  @  behavior shift2:
  @    assumes a == 2;
  @    ensures lsl3: 0 != ( (a<<(unsigned)(n) ) & ((1 << (1+(unsigned)(n)) ))); 
*/
int lshift(int a,int n) { return a << n ; }

/*@ ensures \result == (int) (a >> n) ;
  @  behavior shift1:
  @    assumes n == 3;
  @    ensures lsr1: ((a & 8) != 0) == (0 != (\result & 1));
*/
int rshift(int a,int n) { return a >> n ; }

/*@ behavior true:
  @   assumes a == 1 || b == 1;
  @   ensures \result == 1;
  @  behavior false:
  @   assumes !(a == 1 || b == 1);
  @   ensures \result == 0;
 */
_Bool bor_bool(_Bool a, _Bool b) { return (_Bool)(((int)a | (int)b) != 0); }


/*@ behavior true:
  @   assumes a == 1 && b == 1;
  @   ensures \result == 1;
  @  behavior false:
  @   assumes !(a == 1 && b == 1);
  @   ensures \result == 0;
 */
_Bool band_bool(_Bool a, _Bool b) { return (_Bool)(((int)a & (int)b) != 0); }

/*@ behavior true:
  @   assumes (a == 1 && b == 0) || (a == 0 && b == 1);
  @   ensures \result == 1;
  @  behavior false:
  @   assumes !((a == 1 && b == 0) || (a == 0 && b == 1)) ;
  @   ensures \result == 0;
 */
_Bool bxor_bool(_Bool a, _Bool b) { return (_Bool)(((int)a ^ (int)b) != 0); }

void lemma(unsigned a, unsigned b, unsigned k) {
  //@ check zbit: a1: ~(a + ~a)  == 0;
  //@ check zbit: a2: ~(a | ~a)  == 0;
  //@ check zbit: a3:  (a & ~a)  == 0;
  //@ check           ~(a ^ ~a)  == 0;
  //@ check            (a ^  a)  == 0;
  //@ check           (~a --> a) == a;
  //@ check           (a --> ~a) == ~a;
  //@ check           (~a == ~b) ==> (a == b);

  //@ check zbit: a4: ( a & b & 0xFF ) == ( (a & b) % 0x100 );
  /* note: a5 is not simplified because Qed cannot infer that a&b is positive
   */

  //@ check           ( a & ((b & 0xFFFF) % 55) & 0xFF ) == ( (a & ((b & 0xFFFF) % 55)) % 0x100 );

  //@ check zbit: a5: ( a & b & 77 & ((1 << k)-1) ) == ( (a & b & 77) % (1 << k) );
  /* note: a4 is not simplified because Qed cannot infer that k is positive
   */

  //@ check           ( a & b & 77 & ((1 << (k & 55))-1) ) == ( (a & b & 77) % (1 << (k & 55)) );

}

//@ axiomatic Def { predicate P(integer x); }


//@ ensures \result == (x & 0xFF) ;
unsigned char cast_uchar(int x) {
  unsigned char c = x;
  //@ check bit_test:       ok: (c & (1 << 1)) == 0  ==> (c & 5) == (c & 7);
  //@ check bit_test1:      ok: (c & (1 << 1)) == 0  ==> (P(c & 5) <==> P(c & 7));
  //@ check bit_unset:      ok: (c & 0x77) == 0x66 ==> (x & 1) == 0 ;
  //@ check bit_set_unset:  ok: (c & 0x77) == 0x66 && (x & 5) == (x & 7) ==> (x & 4) == (x & 6) ;
  //@ check bit_set_unset2: ok: (c & 0x77) == 0x66 && (x & 5) == (x & 7) ==> (P(x & 4) <==> P(x & 6)) ;

  //@ check bit_defined:    ok: (c & 0x77) == 0x66 && (x & ~0x77) == (~0x77 & 0xFFF0) ==> (P(c)<==>P(0xE6));
  //@ check bit_defined2:   ok: (c & 0x77) == 0x66 && (x & ~0x77) == (~0x77 & 0xFFF0) ==> (P(x)<==>P(0xFFE6));

  //@ check bit_to_signed_positive:  ok: (x & 0xFF) == 0x60 ==> (P((signed char) x) <==> P(0x60));
  //@ check bit_to_signed_positive2: ok: (x & 0xF0) == 0x60 ==> (((signed char) x) & (1 << 10)) == 0;
  //@ check bit_to_signed_negative:  ok: (x & 0xFF) == 0x86 ==>  (P((signed char) x) <==> P(0x86|~255));
  //@ check bit_to_signed_negative2: ok: (x & 0xF0) == 0x80 ==> (((signed char) x) & (1 << 10)) != 0;
  //@ check bit_to_signed:           ok: (x & 0x0F) == 0x06 ==> (((signed char) x) & (1 << 3)) == 0;
  //@ check bit_to_signed2:          ok: (x & 0x0F) == 0x06 ==> (((signed char) x) & (1 << 2)) != 0;

  //@ check bit_lsl_lowest:          ok: ((x<<2) & 0x0F) != 0x03 ;
  //@ check bit_lsl_higher_set:      ok: ((x<<2) & 0xFF) == (0x0F & ~0x03) ==> (x & 0x03) != 0 ;
  //@ check bit_lsl_higher_unset:    ok: ((x<<2) & 0xFF) == (0x0F & ~0x03) ==> (x & (0xFF>>2) & ~0x03) == 0 ;

  //@ check bit_lsr_set:             ok: ((x>>2) & 0xFF) == (0x0F & ~0x03) ==> (x & 0x30) != 0 ;
  //@ check bit_lsr_unset:           ok: ((x>>2) & 0xFF) == (0x0F & ~0x03) ==> (x & ((0xFF<<2) & ~0x30)) == 0 ;
  return c;
}
