#! /bin/sh

E_ACSL_LIB=`frama-c -print-share-path`/e-acsl

gcc -c pow.c

gcc -std=c99 -pedantic -Wall -Wno-long-long -Wno-attributes -Wno-unused-but-set-variable -fno-builtin -o ./demo pow.o $E_ACSL_LIB/e_acsl.c $E_ACSL_LIB/memory_model/e_acsl_bittree.c $E_ACSL_LIB/memory_model/e_acsl_mmodel.c res_demo.c

./demo
