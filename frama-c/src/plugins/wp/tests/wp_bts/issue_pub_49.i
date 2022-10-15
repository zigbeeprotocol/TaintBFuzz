/*
  Postcondition postcs of function caller1 is proven (fixed value for codeCursor) while codeCursor may be updated in function is_class.
  Similar issue for caller2.
  Hint: proof not achieved when instruction at label_useless_cond is removed as in caller3.
  Hint: proof not achieved when t3 is not declared in the block as in caller4.
  Used command to run the proof:  
    frama-c-gui assigns_postconditions.c -wp -wp-check-memory-model -wp-rte 
*/



int codeCursor;

/*@ 
  assigns codeCursor; 
*/
int is_class(void){
  if (codeCursor < 10)
    codeCursor++;
  return 0;
}


/*@ 
  assigns codeCursor; 
  ensures postcs: codeCursor == \old(codeCursor);
*/
int caller1(void){
  int t1=1;
  int t2=0;
  int t3;
  
  label_useless_cond: if (t1 == 7) return 1;
  
  label_cond_1: if (t2 == 0) {int t3 = is_class(); return t3;}
  //label_cond_2:if (t2 == 0) {t3 = is_class(); return t3;} 
  else return is_class();
}


/*@ 
  assigns codeCursor; 
  ensures postcs: codeCursor == \old(codeCursor);
*/
int caller2(void){
  int t1=1;
  int t2=0;
  int t3;
  
  label_useless_cond: if (t1 == 7) return 1;
  
  label_cond_1: if (t2 == 0) {return is_class();}
  //label_cond_2:if (t2 == 0) {t3 = is_class(); return t3;} 
  else return is_class();
}


/*@ 
  assigns codeCursor; 
  ensures postcs: codeCursor == \old(codeCursor);
*/
int caller3(void){
  int t1=1;
  int t2=0;
  int t3;

  //label_useless_cond: if (t1 == 7) return 1;
   
  label_cond_1: if (t2 == 0) {int t3 = is_class(); return t3;}
  //label_cond_2:if (t2 == 0) {t3 = is_class(); return t3;} 
  else return is_class();
}


/*@ 
  assigns codeCursor; 
  ensures postcs: codeCursor == \old(codeCursor);
*/
int caller4(void){
  int t1=1;
  int t2=0;
  int t3;
  
  label_useless_cond: if (t1 == 7) return 1;
  
  //label_cond_1: if (t2 == 0) {int t3 = is_class(); return t3;}
  label_cond_2:if (t2 == 0) {t3 = is_class(); return t3;} 
  else return is_class();
}

