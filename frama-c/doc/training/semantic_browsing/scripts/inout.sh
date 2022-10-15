#! /bin/sh

emacs ../demos/deps/deps.c &
./run.sh "frama-c -deps -inout -input -out" deps deps.c
