/*@ logic integer id(integer x) = x; */

/*@ lemma test1: 55 == \sum(1,10,id); */

/*@ lemma test2: 5 == \let x = (\lambda integer y; y); x(5); */

/*@ lemma test3: 55 == \sum(1,10,\lambda integer y; y); */

/*@ lemma test4: 55 == \let x = (\lambda integer y; y); \sum(1,10,x); */
