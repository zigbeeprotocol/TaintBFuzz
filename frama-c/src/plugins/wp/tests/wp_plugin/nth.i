/* run.config_qualif
   OPT:
*/

/*@
  axiomatic Def {

  logic integer f(integer a);
  logic integer N;
  logic integer M;
  logic \list<integer> S;
  logic \list<integer> A;
  logic \list<integer> B;
  logic \list<integer> C;

  logic \list<integer> empty = \Nil;
  predicate IsEmpty(\list<integer> s) = s == empty;

  predicate P(\list<integer> s) reads \nothing;

  }
*/

/*@
  axiomatic MkRepeat {

  check lemma negative_repeat: ok: P( A *^ 0 ) <==> P( S *^ (-1) ) ;
  check lemma repeat_nil:      ok: P( A *^ 0 ) <==> P( (S *^ 0) *^ N );
  check lemma repeat_one:      ok: P( S *^ 1 ) <==> P( S );
  check lemma repeat_repeated: ok: P( (S *^ ((N&1)) *^ (M&2)) ) <==> P( S *^ ((N&1) * (M&2)) );

  }
*/

/*@
  axiomatic Equality {

  check lemma constructor_elt: ok: [| 1 |] != [| 2 |] ;

  check lemma not_nil_elt: ok: ([| 1 |] ^ A) != A ;


  check lemma repeat1: ok: (S *^ N) == (S *^ M)
                      <==> (  N == M || ( ((S *^ N) ^ A) == A && ((S *^ M) ^ A) == A ) ) ;

  check lemma repeat2: ok: ( ((S *^ N) ^ S) *^ M ) == ( ( S ^ (S *^ N)) *^ M ) ;

  check lemma left_shift_repeat1:   ok: ( ((S ^ A ^ B) *^ N) ^ S ^ A ) == (S ^ C)
                                   <==> ( (    (A ^ B ^ S) *^ N) ^ A ) == (    C);
  check lemma left_unfold_repeat1:  ok: ( ((S ^ A ^ B) *^ 3) ^ A ^ S ) == (S ^ C)
                          <==> (  A ^ B ^ ((S ^ A ^ B) *^ 2) ^ A ^ S ) == (    C);

  check lemma right_shift_repeat1:  ok: ( A ^ S ^ ((B ^ A ^ S) *^ N) ) == (C ^ S)
                                   <==> ( A ^ ((S ^ B ^ A    ) *^ N) ) == (C    );
  check lemma right_unfold_repeat1: ok: ( S ^ A ^ ((B ^ A ^ S) *^ 3) ) == (C ^ S)
                            <==> ( S ^ A ^ ((B ^ A ^ S) *^ 2) ^ B ^ A) == (C    );


  check lemma left_shift_repeat2:   ok: ( ((S ^ A ^ B) *^ N) ^ S ^ A ^ C) == (S ^ A)
                                   <==> ( (C ^ S) == S && (N<=0 || (A ^ B ^ S ^ S) == S) );
  check lemma left_unfold_repeat2:  ok: ( ((S ^ A ^ B) *^ 3) ^         C) == (S ^ A)
                                   <==> (A ^ A ^ B ^ C ^ S) == A ;

  check lemma right_shift_repeat2:  ok: ( C ^ A ^ S ^ ((B ^ A ^ S) *^ N) ) == (A ^ S)
                                   <==> ( (C ^ S) == S && (N<=0 || (A ^ B ^ S ^ S) == S) );
  check lemma right_unfold_repeat2: ok: ( C ^         ((B ^ A ^ S) *^ 3) ) == (A ^ S)
                                   <==> (A ^ B ^ C ^ S ^ S) == S ;


  check lemma subsequence1: ok: ( A ^ (S *^ N) ^ B ^ S ^ C ) == ( (S *^ N) ^ S )
                           <==> ( A ^ B ^ C ^ C ) == C ;

  }
*/

/*@
  axiomatic Nth {

  check lemma nth_repeat_undefined_1: ko: \nth (  [| f(0), f(1), f(2), f(3) |] *^ 3, 12 ) ==  f(0);

  check lemma nth_repeat_1: ok: \nth (  [| f(0), f(1), f(2), f(3) |] *^ 3, 0 ) ==  f(0);
  check lemma nth_repeat_2: ok: \nth (  [| f(0), f(1), f(2), f(3) |] *^ 3, 11 ) ==  f(3);
  check lemma nth_repeat_3: ok: \nth ( ([| f(0), f(1), f(2), f(3) |] *^ 3) ^ [| f(12) |] , 12 ) ==  f(12);
  check lemma nth_repeat_4: ok: \nth ( ([| f(0), f(1), f(2), f(3) |] *^ 3) ^ [| f(12),f(13),f(14)|] ^ S, 13 ) ==  f(13);

  lemma access_16_16: ok:
  \forall integer k ; 0 <= k < 16 ==>
    f(k)==\nth([| f(0), f(1), f(2),  f(3),  f(4),  f(5),  f(6),  f(7),
                  f(8), f(9), f(10), f(11), f(12), f(13), f(14), f(15) |], k);

  lemma access_4_4: ok:
  \forall integer k ; 0 <= k < 4 ==>
    f(k)==\nth([| f(0), f(1), f(2),  f(3) |], k);

  lemma eq_repeat_concat_3: ok: (S *^ 3) == (S ^ S ^ S) ;

  lemma access_repeat_concat_3: ok: lack:
      \forall integer k ; 0 <= k < 3*\length(S) ==> \nth(S *^ 3, k) == \nth(S ^ S ^ S, k) ;

  }


*/
