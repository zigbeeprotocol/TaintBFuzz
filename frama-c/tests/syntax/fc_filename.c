const char* test = "string concatenation test: " __FC_FILENAME__ ". end test";

int f() {
  return test[2] == 'r';
}

/*@ lemma test: "string cst in ACSL: " __FC_FILENAME__ ".end test"[3] == 'i'; */
