/* run.config
   OPT: -wp-no-print -wp-rte
*/

/* run.config_qualif
   OPT: -then -wp-rte -wp
*/

#include <stdint.h>
#include <string.h>
#include <stdio.h>

/*@ requires validStrings: valid_read_string(s1) && valid_read_string(s2);
    assigns \nothing ;
    allocates \nothing ;
    frees \nothing ;
    exits never: \false ;
    behavior allEqual:
        assumes \forall integer k; 0 <= k <= strlen(s1) ==> s1[k] == s2[k];
        ensures \result == 0;
    behavior SomeDifferent:
        assumes \exists integer k; 0 <= k <= strlen(s1) && s1[k] != s2[k];
        ensures \result != 0;

    disjoint behaviors;
    complete behaviors; */
int stringCompare(const char* s1, const char* s2) {
    if (s1 == s2)
        return 0;

    /*@ loop invariant strlen_s1: 0 <= strlen(s1) <= \at(strlen(s1), Pre);
        loop invariant strlen_s2: 0 <= strlen(s2) <= \at(strlen(s2), Pre);
        loop invariant gauge_s1: s1 + strlen(s1) == \at(s1 + strlen(s1), Pre);
        loop invariant gauge_s2: s2 + strlen(s2) == \at(s2 + strlen(s2), Pre);
        loop invariant gauge: \at(strlen(s1), Pre) - strlen(s1) == \at(strlen(s2), Pre) - strlen(s2);
        loop invariant equal: \forall integer j; 0<= j < \at(strlen(s1), Pre) - strlen(s1) ==> \at(s1,Pre)[j] == \at(s2,Pre)[j];
        loop invariant not_eos: \forall integer j; 0<= j < \at(strlen(s1), Pre) - strlen(s1) ==> \at(s1,Pre)[j] != 0;
        loop assigns s1, s2; */
    while (*s1 == *(s2++))
    {
      if (*(s1++) == '\0') {
        //@ assert length: strlen(s1-1) == strlen(s2-1) == 0;
         return 0;
      }
    }

    //@ assert different: \let k = \at(strlen(s1), Pre) - strlen(s1) ; \at(s1,Pre)[k] != \at(s2,Pre)[k];
    return *(s1) - *(--s2);
}

/*@ requires validString: valid_string(str);
    requires validLength: 0 <= strlen(str) < SIZE_MAX;
    assigns \nothing ;
    exits never: \false ;
    ensures rightResult: \result == strlen(\old(str));
    ensures rightEndCharacter: str[\result] == '\0' ;  */
size_t stringLength(const char* str) {
  const char* s = str ;

  /*@ loop assigns s ;
      loop invariant s + strlen(s) == \at(str + strlen(str),Pre);
      loop invariant 0 <= strlen(s) <= \at(strlen(str),Pre); */
  while (*s++ != '\0');
  return --s - str;
}

/*@ assigns \nothing ;
    exits never: \false ;
    ensures \result != 0 ;*/
int main(void) {

   const char hello[] = { 'h', 'e', 'l', 'l', 'o', '\0'};
   const char helli[] =  { 'h', 'e', 'l', 'l', 'i', '\0'};

   /*@ assert \valid_read(&hello[0]) && \valid_read(&helli[0]) ; */
   return stringCompare(hello, helli);
} 
