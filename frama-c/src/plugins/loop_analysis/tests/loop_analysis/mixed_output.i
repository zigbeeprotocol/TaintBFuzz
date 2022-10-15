void straight_line() {
  int a = 4;
  int b = 2;
  int res = a << 2 + b;
}

void with_if() {
  int a = 3;
  int b = 1;
  int res;
  if (a > b + 1) {
    res = 6;
  }
  res = 7;
}

void loop0() {
  int i;
  for (i = 0; i < 0; i++);
}

void loop1() {
  int i;
  for (i = 0; i < 1; i++);
}

void loop10() {
  int i;
  for (i = 0; i < 10; i++);
}

void loop10init() {
  int i;
  for (i = 3; i < 10; i++);
}

void loop10initneg() {
  int i;
  for (i = 3; i > -10; i--);
}


void loop10initnegle() {
  int i;
  for (i = 3; i >= -10; i--);
}




void loop_inf() {
  unsigned i;
  for (i = 0; i != 10; i--);
}

void loop_inf2() {
  unsigned i;
  for (i = 0; i < 10; i--);
}

void loop108() {
  unsigned i, j;
  int s = 0;
  for (i = 0; i < 10; i++) {
    if (i < 5) {
      s++;
    }
    for (j = 0; j < 10; j++) {
      if (j < i) {
        s++;
      }
    }
  }
}

volatile int nondet;
void loop_large() {
  unsigned i, j, k, l;
  int s = 0;
  for (i = 0; i < 1000000; i++) {
    if (i < 5) {
      s++;
    }
    for (j = 0; j < 1000000; j++) {
      if (j < i) {
        s++;
      }
      for (k = 0; k < 1000000; k++) {
        if (k < j) {
          s++;
        }
        for (l = 0; l < 1000000; l++) {
          if (l < k) {
            s++;
          }
        }
      }
    }
  }
}

void m01() {
  for (int i = 9; i < 30; i += 3); // 7 iterations
}

void m02() {
  for (int i = 9; i <= 30; i += 3); // 8 iterations
}

void m03() {
  for (int i = 10; i < 30; i += 3); // 7 iterations
}

void m04() {
  for (int i = 10; i <= 30; i += 3); // 7 iterations
}

void m05() {
  for (int i = -15; i < 5; i += 3); // 7 iterations
}

void m06() {
  for (int i = -15; i <= 5; i += 3); // 7 iterations
}

void m07() {
  for (int i = -15; i < 6; i += 3); // 7 iterations
}

void m08() {
  for (int i = -15; i <= 6; i += 3); // 8 iterations
}

void m09() {
  for (int i = 30; i > 9; i -= 3); // 7 iterations
}

void m10() {
  for (int i = 30; i >= 9; i -= 3); // 8 iterations
}

void m11() {
  for (int i = 30; i > 10; i -= 3); // 7 iterations
}

void m12() {
  for (int i = 30; i >= 10; i -= 3); // 7 iterations
}

void m13() {
  for (int i = 5; i > -15; i -= 3); // 7 iterations
}

void m14() {
  for (int i = 5; i >= -15; i -= 3); // 7 iterations
}

void m15() {
  for (int i = 6; i > -15; i -= 3); // 7 iterations
}

void m16() {
  for (int i = 6; i >= -15; i -= 3); // 8 iterations
}

void m17() {
  for (int i = 2; i <= 4; i += 3); // 1 iteration
}

void m18() {
  for (int i = 2; i < 4; i += 3); // 1 iteration
}

void m19() {
  for (int i = 4; i >= 2; i -= 3); // 1 iteration
}

void m20() {
  for (int i = 4; i > 2; i -= 3); // 1 iteration
}

void m21() {
  for (int i = 4; i <= 2; i += 3); // 0 iteration (but 1 for the function)
}

void m22() {
  for (int i = 4; i < 2; i += 3); // 0 iteration (but 1 for the function)
}

void m23() {
  for (int i = 2; i >= 4; i -= 3); // 0 iteration (but 1 for the function)
}

void m24() {
  for (int i = 2; i > 4; i -= 3); // 0 iteration (but 1 for the function)
}

void m_01() {
  for (int i = 9; 30 > i; i += 3); // 7 iterations
}

void m_02() {
  for (int i = 9; 30 >= i; i += 3); // 8 iterations
}

void m_03() {
  for (int i = 10; 30 > i; i += 3); // 7 iterations
}

void m_04() {
  for (int i = 10; 30 >= i; i += 3); // 7 iterations
}

void m_05() {
  for (int i = -15; 5 > i; i += 3); // 7 iterations
}

void m_06() {
  for (int i = -15; 5 >= i; i += 3); // 7 iterations
}

void m_07() {
  for (int i = -15; 6 > i; i += 3); // 7 iterations
}

void m_08() {
  for (int i = -15; 6 >= i; i += 3); // 8 iterations
}

void m_09() {
  for (int i = 30; 9 < i; i -= 3); // 7 iterations
}

void m_10() {
  for (int i = 30; 9 <= i; i -= 3); // 8 iterations
}

void m_11() {
  for (int i = 30; 10 < i; i -= 3); // 7 iterations
}

void m_12() {
  for (int i = 30; 10 <= i; i -= 3); // 7 iterations
}

void m_13() {
  for (int i = 5; i < -15; i -= 3); // 7 iterations
}

void m_14() {
  for (int i = 5; i <= -15; i -= 3); // 7 iterations
}

void m_15() {
  for (int i = 6; i < -15; i -= 3); // 7 iterations
}

void m_16() {
  for (int i = 6; i <= -15; i -= 3); // 8 iterations
}

void m_17() {
  for (int i = 2; 4 >= i; i += 3); // 1 iteration
}

void m_18() {
  for (int i = 2; 4 > i; i += 3); // 1 iteration
}

void m_19() {
  for (int i = 4; 2 <= i; i -= 3); // 1 iteration
}

void m_20() {
  for (int i = 4; 2 < i; i -= 3); // 1 iteration
}

void m_21() {
  for (int i = 4; 2 <= i; i += 3); // 0 iteration (but 1 for the function)
}

void m_22() {
  for (int i = 4; 2 < i; i += 3); // 0 iteration (but 1 for the function)
}

void m_23() {
  for (int i = 2; 4 <= i; i -= 3); // 0 iteration (but 1 for the function)
}

void m_24() {
  for (int i = 2; 4 < i; i -= 3); // 0 iteration (but 1 for the function)
}

int main() {
  straight_line();
  with_if();
  loop0();
  loop1();
  loop10();
  loop10init();
  loop10initneg();
  loop10initnegle();
  loop_inf();
  loop108();
  loop_large();
  return 0;
}
