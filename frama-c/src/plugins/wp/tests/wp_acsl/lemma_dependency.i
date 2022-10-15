typedef unsigned char uchar;

/*@ axiomatic A {
    axiom dependency:
      \forall uchar a, b, c; ((a ^ b) & c) <==> ((a & c) ^ (b & c));
    }
*/

/*@ lemma depends:
      \forall uchar a, b, c; ((a ^ b) & c) ==> ((a & c) ^ (b & c));
*/



