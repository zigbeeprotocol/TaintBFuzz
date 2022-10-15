#!/bin/bash -eu

# Checks for extraneous, leftover oracle files that are no longer necessary.
# Only reports files in plugins with a ptests_config file, and in directories
# tested according to that ptests' DEFAULT_SUITES.

echo "Checking for extraneous oracles..."

# TODO: this script currently calls ptests twice for each test case,
# which is unnecessary, but it is fast in practice, so it does not matter

# emulates part of the 'realpath' command, unavailable in MacOS
realpath() {
    [[ $1 = /* ]] && echo "$1" || echo "$PWD/${1#./}"
}

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# absolute path to temporary files
exp_oracles=$(realpath expected_oracles.txt)
actual_oracles=$(realpath actual_oracles.txt)

rm -f $exp_oracles
rm -f $actual_oracles

PTESTS_OPT="${DIR}/../bin/ptests.opt"

# only plug-ins with a ptests_config file are tested
plugins_to_test=$(for d in $(find . -name "ptests_config"); do dirname "$d"; done)
for plugin_test_dir in ${plugins_to_test[@]}
do
    plugin_test_dir=${plugin_test_dir#./}
    plugin_name=${plugin_test_dir#src/plugins/}
    plugin_name=${plugin_name%tests}
    plugin_name=${plugin_name%/}
    plugin_name=${plugin_name:-kernel} # name for the root tests directory
    exp_oracles_plugin=$(realpath "expected_oracles_${plugin_name}.txt")
    rm -f $exp_oracles_plugin
    (cd $plugin_test_dir/..
     test_configs=("<default>" $(find . -mindepth 2 -maxdepth 2 -regex ".*/test_config_[a-zA-Z0-9_].*" | grep --color=none test_config_ | sed 's|.*/test_config_||'))
     for test_config in ${test_configs[@]}
     do
         config_flag=
         if [ ! "$test_config" = "<default>" ]; then
             config_flag="-config $test_config"
         fi
         #echo "Collecting $plugin_name oracles for config $test_config..."
         $PTESTS_OPT $config_flag -dry-run -v \
             | sed -n -E "s|.* >tests/([^ ]+.res.log).*|$plugin_test_dir/\1|p" >> $exp_oracles_plugin
         $PTESTS_OPT $config_flag -dry-run -v \
             | sed -n -E "s|.* 2?>tests/([^ ]+.err.log).*|$plugin_test_dir/\1|p" >> $exp_oracles_plugin
     done
     sort -u $exp_oracles_plugin >> $exp_oracles
     rm $exp_oracles_plugin

     # only report oracles in tested directories (DEFAULT_SUITES)
     for dir in $(grep DEFAULT_SUITES "tests/ptests_config" | sed 's/DEFAULT_SUITES=//'); do
         find "tests/$dir" -name "*.oracle" | sed "s|^|${plugin_test_dir%tests}|" | sed 's|"|\\"|g' >> $actual_oracles
     done
    )
done

sed -i.tmp 's|/result|/oracle|' $exp_oracles
sed -i.tmp 's|\.log|\.oracle|' $exp_oracles
rm -f $exp_oracles.tmp

# note: sort allows output to the same input file
sort -u $exp_oracles -o $exp_oracles
sort -u $actual_oracles -o $actual_oracles

# Note: we could report missing oracles (in expected, but not in actual),
# but OCI and users in general do not test all alternative configurations.

nb_extra=$(comm -13 $exp_oracles $actual_oracles | wc -l)
if [ "$nb_extra" -eq 0 ]; then
    echo "No extraneous oracles found."
else
    echo "=== Extraneous oracles found! ==="
    comm -13 $exp_oracles $actual_oracles
    echo "=== Total: $nb_extra extraneous oracles ==="
fi

rm -f $exp_oracles
rm -f $actual_oracles

if [ $nb_extra -ne 0 ]; then
    exit 1
fi
