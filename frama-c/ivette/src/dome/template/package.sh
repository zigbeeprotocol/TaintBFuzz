#!/bin/sh

# --------------------------------------------------------------------------
# ---  Compute mode
# --------------------------------------------------------------------------

OPT=""
LOG=""

case $1 in
    "--dev"|"-D")
        OPT="--dev"
        LOG=".dome-pkg-dev"
        shift
        ;;
    "--app"|"-A")
        OPT=""
        LOG=".dome-pkg-app"
        shift
        ;;
    *)
        echo "Require --dev or --app option"
        exit 1
        ;;
esac

# --------------------------------------------------------------------------
# ---  Check for Updates
# --------------------------------------------------------------------------

rm -f $LOG.tmp
echo $* > $LOG.tmp

if [ -f $LOG.lock ]
then
    diff $LOG.tmp $LOG.lock
    if [ $? -eq 0 ]
    then
        rm -f $LOG.tmp
        echo "Packages are up-to-date."
        exit 0
    fi
fi

# --------------------------------------------------------------------------
# ---  Updates Packages
# --------------------------------------------------------------------------

echo "yarn add $OPT $*"
yarn add $OPT $*

if [ $? -eq 0 ]
then
    mv -f $LOG.tmp $LOG.lock
else
    echo "Package installation failed."
    exit 1
fi

# --------------------------------------------------------------------------
