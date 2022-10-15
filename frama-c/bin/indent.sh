# Help

case "$1" in
    "-h"|"--help")
        echo "indent [-h|--help] [DIR|FILE]"
        echo ""
        echo "  Re-indent and remove trailing spaces in OCaml sources."
        echo "  By default, find sources in '.', but can be applied on a"
        echo "  directory or on a single file."
        echo ""
        echo "  Only applies to writable '*.ml' and '*.mli' files."
        exit 0 ;;
esac

# Root file or directory

ROOT="."
if [ "$1" != "" ]
then
    ROOT="$1"
fi

# re-indent and de-spacify all files

for file in $(find $ROOT \( -name "*.ml" -or -name "*.mli" \) -perm -u+w); do
    if file $file | grep -wq "ISO-8859"; then
        echo "Convert $file";
        iconv -f ISO-8859-1 -t UTF-8 $file > $file.tmp;
        mv $file.tmp $file;
    fi;
    echo "Indent  $file"
    sed -e's/[[:space:]]*$//' $file > $file.tmp;
    mv $file.tmp $file;
    ocp-indent -i $file;
done
