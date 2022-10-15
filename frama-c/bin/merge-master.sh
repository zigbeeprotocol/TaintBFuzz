#!/bin/sh

if test -z "$1"; then
    echo "Syntax: $0 <release name>";
    exit 1
fi

# Name of the release branch to merge in master
BRANCH="stable/$1"

# Last merge commit between master and the release
ANCESTOR=$(git merge-base $BRANCH master)

# Find Gitlab text ('See merge request') and extract merge numbers
MR=$(git log --format='%b' --merges $ANCESTOR..$BRANCH \
            | sed -n 's/See merge request \(![0-9]*\)/\1/p' \
            | tr '\n' ' ' )

git merge $BRANCH -m "Merging $BRANCH into master ($MR)"
