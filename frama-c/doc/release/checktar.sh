#!/usr/bin/env bash

if [[ "$1" == "" ]]; then
    DIR="."
else
    DIR=${1%/}
fi

ERROR_CODE=0

RESULT=$(find $DIR -name '*NE_PAS_LIVRER*')
if [[ "$RESULT" != "" ]]; then
    echo "### ERROR: The following files should not be distributed:"
    echo $RESULT
    ERROR_CODE=1
fi

RESULT=$(find $DIR -name '*nonfree*' -o -name '*non_free*' -o -name '*non-free*')
if [[ "$RESULT" != "" ]]; then
    echo "### ERROR: The following files should not be distributed:"
    echo $RESULT
    ERROR_CODE=1
fi

PLUGINS=( genassigns mthread volatile acsl-importer caveat-importer cfp security pathcrawler a3export )

for A in ${PLUGINS[@]}
do
    if [ -e $DIR/src/plugins/$A ]; then
        echo "### ERROR: Trying to release plugin: $A"
        ERROR_CODE=1
    fi
done

RESULT=$(grep -Iir $HOME $DIR)

if [[ "$RESULT" != "" ]]; then
    echo "### ERROR: Found some $HOME occurrences in the distribution"
    echo $RESULT
    ERROR_CODE=1
fi

exit $ERROR_CODE
