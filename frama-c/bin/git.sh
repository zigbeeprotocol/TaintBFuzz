ACTION="$*"

if [ "$ACTION" == "" ]
then
    ACTION="status -s -b"
fi

if [ "$1" == "-h" -o "$1" == "--help" ]
then
    echo ""
    echo "Multi-repository git broadcast"
    echo ""
    echo "  git.sh -h|--help"
    echo "  git.sh clone <repo> <dir>"
    echo "  git.sh remove <dir>"
    echo "  git.sh <command>"
    echo ""
    echo "The form 'git.sh clone <repo> <dir>' performs"
    echo "an inner clone of <repo> inside <dir> sub-directory"
    echo "and add <dir> to the excluded directories of the root."
    echo ""
    echo "The form 'git.sh remove <dir>' removes the git"
    echo "clone at <dir>, if any."
    echo ""
    echo "Otherwize, 'git.sh <command>' broadcast the command"
    echo "to all '.git' repository accessible from the root."
    echo "The default command is 'git.sh status -s -b'."
    echo ""
    exit 0
fi

if [ "$1" == "remove" ]
then
    if [ "$2" == "" ]
    then
        echo "git.sh remove <directory>"
        exit 2
    fi
    if [ ! -d "$2/.git" ]
    then
        echo "Missing git repository $2/.git"
        exit 2
    fi
    echo "--------------------------------------------------"
    echo "-- Removing ./$2"
    echo "--------------------------------------------------"
    rm -fr $2
    grep -v "/$2" .git/info/exclude > .tmp
    mv .tmp .git/info/exclude
    cat .git/info/exclude
    ACTION="status -s -b"
fi

if [ "$1" == "clone" ]
then
    if [ "$2" == "" -o "$3" == "" ]
    then
        echo "git.sh clone <repository> <directory>"
        exit 2
    fi
    echo "--------------------------------------------------"
    echo "-- Repository ./$3"
    echo "--------------------------------------------------"
    echo "Cloning $2"
    mkdir -p $3
    (cd $3 && git clone $2 .)
    echo "--------------------------------------------------"
    echo "--- .git/info/exclude"
    echo "--------------------------------------------------"
    echo "/$3" >> .git/info/exclude
    cat .git/info/exclude
    ACTION="status -s -b"
fi

for pgit in `find . -type d -name .git`
do

    plugin=`dirname $pgit` ;

    echo "--------------------------------------------------"
    echo "-- Repository $plugin"
    echo "--------------------------------------------------"

    git -C $plugin $ACTION

done
echo "--------------------------------------------------"
