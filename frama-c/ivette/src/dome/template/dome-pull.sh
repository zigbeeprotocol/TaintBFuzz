# --------------------------------------------------------------------------
# ---  Pulling Dome Updates
# --------------------------------------------------------------------------

if [ ! -z "$(git status --porcelain)" ]
then
    echo "Local non-commited modifications, aborted."
    exit 1
fi

if [ ! -d .gitdome ]
then
    git clone git@git.frama-c.com:dome/electron.git .gitdome
fi

head=$(git rev-parse --abbrev-ref HEAD)
commit=$(git -C .gitdome rev-parse HEAD)
remote=$(git -C .gitdome rev-parse --abbrev-ref HEAD)

git checkout stable/dome

if [ "$?" != "0" ]
then
    echo "Missing local branch stable/dome, aborted."
    exit 1
fi

echo "Pulling Dome updates from $remote to stable/dome..."
git -C .gitdome pull --prune

for f in $(git -C .gitdome ls-files)
do
    mkdir -p $(dirname $f)
    cp -f .gitdome/$f $f
    git add $f
done

if [ ! -z "$(git status --porcelain)" ]
then
    git commit -m "[Dome] $commit"
    echo "Dome repository updated."
    git checkout $head
    echo "Merging Dome updates..."
    git merge stable/dome
else
    echo "Dome is already up-to-date."
    git checkout $head
fi

# --------------------------------------------------------------------------
