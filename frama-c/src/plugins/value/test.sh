#!/bin/bash
export GCC3264=-m32
export FRAMAC3264=x86_32
#export GCC3264=
#export FRAMAC3264=x86_64
export REPORT=$CSMITH
while true
do
$CSMITH/src/csmith --max-expr-complexity 15 --max-pointer-depth 3 --max-funcs 4 --max-array-dim 2 --max-array-len-per-dim 3 --max-struct-fields 12 --max-union-fields 12 --no-volatiles --no-bitfields --no-argc --unions > t$N.c
gcc -C -E -I$CSMITH/runtime -D__FRAMAC__ $GCC3264 t$N.c -o t$N.i
gcc $GCC3264 -pipe t$N.i $CSMITH/show_each-$FRAMAC3264.o -o e$N
( ulimit -S -t 1 ; time ./e$N > res$N.exec ) 2> time$N
rcexec=$?
if [[ $rcexec != 152 && $rcexec != 137 ]] 
then
    if grep "user.0m0.0[01]" time$N
    then
	( ulimit -S -t 18000 -m 2500000 ; exec ~/ppc/bin/toplevel.opt -warn-signed-overflow -eva t$N.i -stop-at-first-alarm -eva-no-show-progress -machdep $FRAMAC3264 -obviously-terminates -precise-unions > res$N.value )
	rc=$?
	if grep imprecise res$N.value
	then  
	    tag=`date "+%d%H%M%S"`
	    cp t$N.c $REPORT/imprecise.$tag.$N.c
	    cp t$N.i $REPORT/imprecise.$tag.$N.i
	    cp res$N.exec $REPORT/imprecise.$tag.$N.exec
	    cp res$N.value $REPORT/imprecise.$tag.$N.res
	    echo $rc > $REPORT/imprecise.$tag.$N.rc
            echo $rcexec > $REPORT/imprecise.$tag.$N.execrc
	elif [[ $rc != 152 && $rc != 137 ]] 
	then
	    if grep assert < res$N.value
            then 
		if [[ $rcexec != 139 ]]
		then
		    tag=`date "+%d%H%M%S"`
		    cp t$N.c $REPORT/assert.$tag.$N.c
		    cp t$N.i $REPORT/assert.$tag.$N.i
		    cp res$N.value $REPORT/assert.$tag.$N.res
		    cp res$N.exec $REPORT/assert.$tag.$N.exec
		    echo $rcexec > $REPORT/assert.$tag.$N.execrc
		fi
	    elif grep Frama_C_show_each < res$N.value | cmp res$N.exec
	    then true
	    else
		tag=`date "+%d%H%M%S"`
		cp t$N.c $REPORT/noresult.$tag.$N.c
		cp t$N.i $REPORT/noresult.$tag.$N.i
		cp res$N.exec $REPORT/noresult.$tag.$N.exec
		cp res$N.value $REPORT/noresult.$tag.$N.res
		echo $rc > $REPORT/noresult.$tag.$N.rc
		echo $rcexec > $REPORT/noresult.$tag.$N.execrc
	    fi
	fi
    fi
fi
done
