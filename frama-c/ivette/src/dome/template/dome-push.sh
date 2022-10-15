# --------------------------------------------------------------------------
# ---  Pulling Dome Updates
# --------------------------------------------------------------------------

branch=$1
app=$(basename $1)

if [ "$branch" == "" ]
then
    echo "Missing branch name, aborted."
    exit 1
fi

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
commit=$(git rev-parse HEAD)
remote=$(git -C .gitdome rev-parse --abbrev-ref HEAD)

echo "[dome] update $branch"
git -C .gitdome fetch --prune
git -C .gitdome checkout $branch

if [ "$?" != "0" ]
then
    git -C .gitdome checkout -b $branch
else
    git -C .gitdome pull --rebase
fi

echo "[dome] push updates from $head to $branch..."

for f in $(git ls-files)
do
    mkdir -p .gitdome/$(dirname $f)
    cp -f $f .gitdome/$f
    git -C .gitdome add $f
done

echo "[dome] commit $branch"
git -C .gitdome commit -e -m "[$app] $commit"
echo "[dome] push $branch"
git -C .gitdome push origin -f -u $branch
echo "[dome] back to $remote"
git -C .gitdome checkout $remote

# --------------------------------------------------------------------------
