#! /bin/sh
frama-c -e-acsl-prepare -save demo.sav demo.c -wp -then -val -slevel 11 -then -e-acsl -then-on e-acsl -print -ocode res_demo.c
