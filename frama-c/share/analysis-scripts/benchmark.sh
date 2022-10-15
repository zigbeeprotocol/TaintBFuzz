#!/bin/bash -eu

# --------------------------------------------------------------------------
# --- Command Line Parsing                                               ---
# --------------------------------------------------------------------------

targets=""
git_hash="master"
clone_dir="frama-c-clones"
comment=""
show_usage=""
repository_path=""
makefile_path="."
output_file="benchmark-results.csv"

while [[ $# > 0 ]]
do
    case $1 in
        -b|--hash|--branch)
            git_hash="$2"
            shift
            ;;

        -d|--clone-dir)
            clone_dir="$2"
            shift
            ;;

        -c|--comment)
            comment="$2"
            shift
            ;;

        -p|--repository-path)
            repository_path="$2"
            shift
            ;;

        -m|--makefile-path)
            makefile_path="$2"
            shift
            ;;

        -o|--output)
            output_file="$2"
            shift
            ;;

        -h|--help)
            show_usage="yes"
            ;;

        *)
            targets="$targets $1"
            ;;
    esac
    shift
done

if [ -z "$targets" -o -n "$show_usage" ]
then
    echo "Usage: $0 TARGET ..."
    echo "Run benchmark for the specified targets."
    echo ""
    echo "The following arguments can be given:"
    echo "  -b, --hash HASH,            selects HASH or BRANCH in the frama-c repository"
    echo "      --branch BRANCH"
    echo "  -d, --clone-dir             path to the directory where frama-c versions are"
    echo "                                cloned"
    echo "  -c, --comment COMMENT       a comment associated to results for better"
    echo "                                readability of the results; if omitted,"
    echo "                                defaults to the Frama-C branch name"
    echo "  -p, --repository-path PATH  do not clone frama-c, use this repository instead"
    echo "  -m, --makefile-path FILE    path to the makefile which can build the target"
    echo "  -o, --output FILE           path to the output CSV file to be filled"
    echo "  -h, --help                  prints this help and quits"
    exit 1
fi

if [ -z "$comment" ]
then
    # Note: if the user gave us a commit hash instead of a branch name,
    #       we do not retrieve the branch name (which may not exist anyway)
    comment="$git_hash"
fi


# --------------------------------------------------------------------------
# --- Frama-C repository                                                 ---
# --------------------------------------------------------------------------

if [ -z "$repository_path" ]
then
    # git_hash and comment cannot be parsed yet:
    # we need the git clone to dereference it, in case it's a tag/branch name

    ##### Preparation of git clones/checkouts #####

    bare="$clone_dir/frama-c.git"

    # Check if bench clone exists
    if [ ! -d "$bare" ]
    then
        echo "Cloning Frama-C..."
        git clone --bare --quiet git@git.frama-c.com:frama-c/frama-c "$bare"
        sed --in-place '/bare = true/d' $bare/config
    fi

    # Fetch all refs
    (
        cd $bare
        git fetch origin '+refs/heads/*:refs/heads/*' --prune
    )

    # Now we can parse the other arguments

    # Resolve branch name if given
    git_hash=`git --git-dir="$bare" rev-parse "$git_hash"`

    # repository_path must be an absolute path
    repository_path="$(readlink -f "$clone_dir/$git_hash")"

    # Checkout and build the branch if necessary
    if [ ! -e "$clone_dir/$git_hash" ]
    then
        echo "Building Frama-C for git commit: $git_hash"
        # The workdir cmd can extract a working tree of the desired hash
        # without cloning once more
        workdir_cmd=`locate git-new-workdir --limit 1`
        if [ -z "$workdir_cmd" ]
        then
            git --git-dir="$bare" worktree add "$repository_path" "$git_hash"
        else
            bash "$workdir_cmd" "$bare" "$repository_path" "$git_hash"
        fi
        # Build Frama-C
        (
            cd "$repository_path";
            autoconf;
            ./configure --disable-wp;
            make -j;
        )
    fi
fi

# In case building has failed for some reason, we check if the actual binary
# exists and report an error otherwise, indicating which directory should be
# deleted.
FRAMAC="$repository_path/bin/frama-c"

if [ ! -e "$FRAMAC" ]
then
    echo "Error: could not find Frama-C binary: $FRAMAC"
    echo "You may try erasing the directory to force a recompilation."
    exit 2
fi


# --------------------------------------------------------------------------
# --- Benchmark execution and output                                     ---
# --------------------------------------------------------------------------

header="target\ttimestamp\tFrama-C hash\tcomment\tcpu_time\tmaxmem\talarms\t\
warnings\tsem reach fun\tsyn reach fun\ttotal fun\tsem reach stmt\t\
syn reach stmt\tcommand args\tcase study git hash"

if [ ! -e "$output_file" ]
then
    echo "output file does not exist, creating: $output_file"
    printf "$header\n" > "$output_file"
fi

for target in $targets
do
  pushd $makefile_path > /dev/null
  make --no-print-directory $target BENCHMARK=y FRAMAC="$FRAMAC"

  case_git_hash=`git rev-parse HEAD`
  . $target/stats.txt
  popd > /dev/null

  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
      "$target" "$timestamp" $git_hash "$comment" \
      $user_time $memory $alarms $warnings \
      $sem_reach_fun $syn_reach_fun $total_fun $sem_reach_stmt $syn_reach_stmt \
      "$cmd_args" $case_git_hash \
      >> "$output_file"

  if command -v sqlite3 2>&1 >/dev/null
  then
    export comment
    export git_hash
    export case_git_hash
    export target
    "${BASH_SOURCE%/*}/bench-sqlite.sh" "$makefile_path/$target/stats.txt"
  else
    echo "command 'sqlite3' not found, cannot update the database"
  fi
done
