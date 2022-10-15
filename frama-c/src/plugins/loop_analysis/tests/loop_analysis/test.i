void main(void)
{
  int i; int j;
  i = 3;
  i ++;
  j = 4;
  int z = 8;
  for(i = 0; i < 10; i++){
    if(j != 3) j++;
  }
}

void k(int i){
  int u;
  if(i) { u = 1; } else {u = 2;}
  u++;
}

void f(int i){
  int u = 0;
  if(i) { u = 1; }
  if(i) { u = 2; }
  if(i) { u = 3; }
  u++;
}

void g(int i){

  int u;
  int j = 0;
  while(j < 10) {
    j++;
    if(i) u = j;
  }
}

void h(void){
  int i = 0;
  while (i < 5 + sizeof(int)) { i++;}
}

void h2(void){
  int i = 0;
  while (i < 5 + 4) { i++;}
}

void h3(int a){
  int i = 0;
  while(i < 20) {if (a) {a++;} i++;}
  i++;
}

void h4(int a){
  int i = 0;
  while(i < 10) {if (a) {a++;} i++;}
  i++;
}

void h5(int a){
  int i = 0; int j = 0;
  while(i < 10) {i++; if (a) {a++;} j = 1;}
  i++;
}

void h6(int a){
  int i = 0; int j = 0;
  while(i < 10) {i++; if (a) {a++;}}
  i++;
}

