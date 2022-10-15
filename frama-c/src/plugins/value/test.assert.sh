#!/bin/bash
export GCC3264=-m32
export FRAMAC3264=x86_32
#export GCC3264=
#export FRAMAC3264=x86_64
export REPORT=$CSMITH
while true
do
$CSMITH/src/csmith --no-checksum --max-expr-complexity 10 --max-pointer-depth 3 --max-funcs 10 --packed-struct --max-array-dim 2 --max-array-len-per-dim 3 --max-struct-fields 12 --max-union-fields 12 --no-volatiles --no-bitfields --no-argc --unions > t$N.c
sed "/platform_main_end/ r $CSMITH/insert_dump_assert" < t$N.c > t$N.a.c
gcc -C -E -I$CSMITH/runtime $GCC3264 t$N.a.c -o t$N.a.i
gcc $GCC3264 -pipe t$N.a.i $CSMITH/dump_assert_nop-$FRAMAC3264.o -o e$N
( ulimit -S -t 1 ; ./e$N > /dev/null )
rcexec=$?
if [[ $rcexec != 127 && $rcexec != 152 && $rcexec != 137 ]] 
then
    ( ulimit -S -t 18000 -m 2500000 ; exec ~/ppc/bin/toplevel.opt -no-collapse-call-cast -slevel-function main:0 -no-results -warn-signed-overflow -eva t$N.a.i -eva-no-show-progress -machdep $FRAMAC3264 -precise-unions > res$N.value )
    rc=$?
    if grep imprecise res$N.value
    then  
	tag=`date "+%d%H%M%S"`
	cp t$N.c $REPORT/imprecise.$tag.$N.c
	cp t$N.a.i $REPORT/imprecise.$tag.$N.i
	cp res$N.value $REPORT/imprecise.$tag.$N.res
	echo $rc > $REPORT/imprecise.$tag.$N.rc
        echo $rcexec > $REPORT/imprecise.$tag.$N.execrc
    elif [[ $rc != 152 && $rc != 137 ]] 
    then
	( echo "exit " ; $CSMITH/selin_assert.pl < res$N.value ; echo ';') > assert$N

	sed "/platform_main_end/ r assert$N" < t$N.c > t$N.b.c
	gcc -C -E -I$CSMITH/runtime $GCC3264 t$N.b.c -o t$N.b.i	
	gcc $GCC3264 -pipe t$N.b.i $CSMITH/dump_assert_nop-$FRAMAC3264.o -o e.b.$N
	./e.b.$N
	rcb=$?
	if [[ $rcb != 1 ]]
	then
	    tag=`date "+%d%H%M%S"`
	    cp t$N.c $REPORT/cassert.$tag.$N.c
	    cp t$N.a.c $REPORT/cassert.$tag.$N.a.c
	    cp t$N.a.i $REPORT/cassert.$tag.$N.a.i
	    cp t$N.b.c $REPORT/cassert.$tag.$N.b.c
	    cp t$N.b.i $REPORT/cassert.$tag.$N.b.i
	    cp e.b.$N  $REPORT/cassert.$tag.$N.e.b
	    cp e.$N    $REPORT/cassert.$tag.$N.e.a
	    cp res$N.value $REPORT/cassert.$tag.$N.res
	    echo $rcexec > $REPORT/cassert.$tag.$N.execrc
	fi
    fi
fi
done
