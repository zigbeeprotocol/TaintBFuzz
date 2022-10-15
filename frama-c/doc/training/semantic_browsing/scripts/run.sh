#! /bin/sh

dir=../demos/$2
command="$1 -cpp-extra-args=\"-I$dir\" $dir/$3"

echo "RUNNING:"
echo "$command"

echo "THE OUTPUT IS:"
eval $command
