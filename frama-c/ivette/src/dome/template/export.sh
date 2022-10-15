#!/bin/bash

# --------------------------------------------------------------------------
# ---  Export Dome API
# --------------------------------------------------------------------------

DOME=$1
COND=''
COND+=' -not -path "*/demo/*"'
COND+=' -not -name "Application.js"'
COND+=' -not -name "Preferences.js"'
COND+=' -not -name "dome.js"'
COND+=' -not -name "index.js"'

FILES=`cd $DOME/src ; find renderer -name "*.js" $COND`

echo "{ let m = require('react'); register('react',m); }"
echo "{ let m = require('dome'); register('dome',m); }"
echo "{ let m = require('dome/system'); register('dome/system',m); }"
for f in $FILES
do
    j=${f/renderer/dome}
    m=${j/.js/}
    echo "{ let m = require('$m'); register('$m',m); }"
done

# --------------------------------------------------------------------------
