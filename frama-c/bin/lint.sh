#!/bin/sh
set -e

# --------------------------------------------------------------------------
# ---  Try to Automate lintage
# --------------------------------------------------------------------------

DEFAULT=yes
# DEFAULT includes BLANKS, TRAILING and INDENT
BLANKS=no
TRAILING=no
INDENT=no
EMACS=no

while test -n "$1" ;
do
    case $1 in
        "-h"|"--help")
            echo "lint.sh [options...] files..."
            echo "  -h,--help        print help and exit"
            echo "  -w,--whitespace  fix white spaces (by default)"
            echo "  -t,--trailing    fix trailing lines (by default)"
            echo "  -i,--indent      fix indentation (by default)"
            echo "  -e,--emacs       use emacs script (fix only whitespace, not by default)"
            exit 0
            ;;
        "-w"|"--whitespace")
            DEFAULT=no
            BLANKS=yes
            ;;
        "-t"|"--trailing")
            DEFAULT=no
            TRAILING=yes
            ;;
        "-i"|"--indent")
            DEFAULT=no
            INDENT=yes
            ;;
        "-e"|"--emacs")
            DEFAULT=no
            EMACS=yes
            ;;
        *)
            if test $BLANKS = yes -o $DEFAULT = yes ;
            then
                echo "Linting (blanks)   $1"
                sed --in-place="" -e 's/^ *\t\+/ /' $1
                sed --in-place="" -e 's/\(.*[^[:blank:]]\)[[:blank:]]\+$/\1/' $1
                sed --in-place="" -e 's/^[ \t]\+$//' $1
            fi
            if test $TRAILING = yes -o $DEFAULT = yes ;
            then
                echo "Linting (trailing) $1"
                if test \( $(tail -n -1 $1 | wc -l) -eq 0 \) -a \( $(wc -c $1 | cut -d " " -f 1) -gt 0 \) ;
                then
                    echo "" >> $1
                else
                    while tail -n -1 $1 | grep -l -e '^[ \t]*$';
                    do
                        head -n -1 $1 > $1.tmp;
                        mv $1.tmp $1
                    done
                fi
            fi
            if test $EMACS = yes ;
            then
                echo "Linting (emacs)    $1"
                emacs --batch $1 \
                      -f mark-whole-buffer \
                      -f untabify \
                      -f delete-trailing-whitespace \
                      -f save-buffer 2> .lint.log
            fi
            if test $INDENT = yes -o $DEFAULT = yes ;
            then
                echo "Linting (indent)   $1"
                ocp-indent -i $1
            fi
            ;;
    esac
    shift
done

echo "Lint done."
