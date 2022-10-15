#! /bin/sh

./run.sh "frama-c-gui -no-frama-c-stdlib -cpp-extra-args='-DSTDC_HEADERS=1 -DHAVE_UNISTD_H=1 -DDIRENT=1'" gzip-1.2.4 *.c
#./run.sh "../../../../bin/viewer.byte" gzip-1.2.4 *.c
#./run.sh "../../../../bin/viewer.opt -no-frama-c-stdlib -cpp-extra-args='-DSTDC_HEADERS=1 -DHAVE_UNISTD_H=1 -DDIRENT=1'" gzip-1.2.4 *.c
#./run.sh "~/frama-c-Beryllium-20090902/bin/viewer.opt" gzip-1.2.4 *.c

