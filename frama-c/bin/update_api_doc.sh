#!/bin/sh

next=$1

if test -z "$next"; then
  echo "Missing argument. Usage is:"
  echo "\$ ./bin/update_api_doc.sh <NEXT>"
  echo "See the Release Management Documentation for an example."
else
  find src -name '*.ml*' -exec sed -i -e "s/Frama-C+dev/${next}/gI" '{}' ';'
fi
