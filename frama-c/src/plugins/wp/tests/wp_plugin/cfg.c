//@ assigns \nothing;
void foo(void);

/*@ ensures BUG_LEGACY_WP: \false; */
void f1(void)
{
  if (0 == 1)
    goto return_label;
  {
    int t1 = 1;
    foo();
    goto return_label;
  }
  return_label: return;
}

/*@ ensures BUG_LEGACY_WP: \false; */
void f1_simpler(void)
{
  if (0 == 1)
    goto return_label;
  {
    int t1 = 1;
    goto return_label;
  }
  return_label: return;
}

/*@ ensures BUG_LEGACY_WP: \false; */
void f1_variant(void)
{
  if (0 == 1) L: ;
  else {
    int t1 = 1;
    foo();
    goto return_label;
  }
  return_label: return;
}

/*@ ensures FAILS_AS_EXPECTED: \false; */
void f1_variant_invert(void)
{
  if (! (0 == 1)) {
    int t1 = 1;
    foo();
    goto return_label;
  }
  else L: ;
  return_label: return;
}

/*@ ensures BUG_LEGACY_WP: \false; */
void f2(void)
{
  if (0 == 1)
    goto L;
  if (0 == 0) {
    int t1 = 1;
    foo();
    goto return_label;
  }
  else L: ;
  return_label: return;
}
