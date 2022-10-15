unsigned int M;

void mean(unsigned int* p, unsigned int* q) {
  M = (*p + *q) / 2;
}

//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie mean.c"
End:
*/
//NOPP-END
