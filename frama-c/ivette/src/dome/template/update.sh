#!/bin/sh

# --------------------------------------------------------------------------
# ---  Update Templated File (merge with user modifications)
# --------------------------------------------------------------------------

USER=$2
TEMPLATE=$1
BACK=$(dirname $USER)/.dome-$(basename $USER).back
ORIGIN=$(dirname $TEMPLATE)/.dome-$(basename $TEMPLATE).orig
DIFF=$(dirname $USER)/.dome-diff

if [ ! -f $TEMPLATE ]
then
    echo "[Dome] missing template ('$TEMPLATE')"
    exit 2
fi

if [ -f $USER ]
then
    if [ ! -f $ORIGIN ]
    then
        echo "[Dome] lost original template for '$USER' (search for diffs)"
        cp -f $TEMPLATE $ORIGIN
    fi
    cp -f $USER $BACK
    rm -f $USER
    diff3 -m -L YOURS $BACK -L ORIGIN $ORIGIN -L TEMPLATE $TEMPLATE > $USER
    MERGED=$?
    cp -f $TEMPLATE $ORIGIN
    if [ $MERGED -eq 0 ]
    then
        diff $USER $BACK > $DIFF
        if [ $? -eq 0 ]
        then
            echo "[Dome] updated '$USER' with new template (no modifications)"
        else
            echo "[Dome] merged '$USER' with new template (backup saved)."
        fi
        rm -f $DIFF
        exit 0
    else
        while true
        do
              echo "[Dome] conflicting '$USER' with new template."
              echo " (d) show diffs   (e) edit conflict"
              echo " (k) keep current (t) use template"
              read -p "Your choice ? [t] " ACTION
              case $ACTION in
                  d)
                      echo "Differences ( > yours, < template ):"
                      diff $TEMPLATE $BACK
                      ;;
                  e)
                      echo "Previous content saved in '$BACK'."
                      echo "Run 'make dome-templ' after '$USER' has been fixed."
                      exit 1
                      ;;
                  k)
                      exit 0
                      ;;
                  t|"")
                      cp -f $TEMPLATE $USER
                      exit 0
                      ;;
              esac
        done
    fi
else
    echo "[Dome] creating '$USER' from template"
    cp -f $TEMPLATE $USER
    cp -f $TEMPLATE $ORIGIN
fi

# --------------------------------------------------------------------------
