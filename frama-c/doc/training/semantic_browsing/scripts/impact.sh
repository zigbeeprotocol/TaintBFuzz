#! /bin/sh

./run.sh "frama-c-gui -no-dynlink -load-module /usr/local/lib/frama-c/plugins/Security_slicing -journal-enable -val -quiet" cruise_control *.c
#./run.sh "../../../../bin/viewer.opt -val -quiet" cruise_control *.c
