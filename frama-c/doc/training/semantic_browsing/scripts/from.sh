#! /bin/sh

emacs ../demos/deps/deps.c &
./run.sh "frama-c -deps" deps deps.c
