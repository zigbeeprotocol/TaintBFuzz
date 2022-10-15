#! /bin/sh
frama-c demo.c -e-acsl -then-on e-acsl -print -ocode res_demo.c
