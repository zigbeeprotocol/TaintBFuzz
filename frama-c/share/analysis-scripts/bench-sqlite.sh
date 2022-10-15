#!/bin/bash -eu

database="benchmark-results.db"
stats="$1"

function query
{
  sqlite3 $database "$@"
}


# --- Database Creation ---

if [ ! -e $database ]
then
  query <<SQL
    CREATE TABLE benchmark_results (
      id ROWID,
      target TEXT NOT NULL,
      timestamp TEXT NOT NULL,
      hash_fc TEXT NOT NULL,
      hash_case TEXT NOT NULL,
      comment TEXT NOT NULL,
      user_time REAL NOT NULL,
      memory INTEGER NOT NULL,
      alarms INTEGER NOT NULL,
      warnings INTEGER NOT NULL,
      sem_reach_fun INTEGER NOT NULL,
      syn_reach_fun INTEGER NOT NULL,
      total_fun INTEGER NOT NULL,
      sem_reach_stmt INTEGER NOT NULL,
      syn_reach_stmt INTEGER NOT NULL,
      command_line TEXT NOT NULL
    );
SQL
fi


# --- Adding record ---

source $stats

query <<SQL
  INSERT INTO benchmark_results(
      target, timestamp, hash_fc, hash_case, comment, user_time, memory,
      alarms, warnings, sem_reach_fun, syn_reach_fun, total_fun,
      sem_reach_stmt, syn_reach_stmt, command_line)
  VALUES(
    "$target", "$timestamp", "$git_hash", "$case_git_hash", "$comment",
    "$user_time", "$memory", "$alarms", "$warnings", "$sem_reach_fun",
    "$syn_reach_fun", "$total_fun", "$sem_reach_stmt", "$syn_reach_stmt",
    "$cmd_args");
SQL


# --- Comparison ---

result=`sqlite3 benchmark-results.db <<SQL
  SELECT 
    printf("%+.1f", 100*$user_time/avg(user_time) - 100),
    printf("%+d", $warnings - min(warnings)),
    printf("%+d", $alarms - min(alarms))
  FROM benchmark_results
  WHERE target='$target';
SQL`
IFS='|' read -r diff_user_time diff_warnings diff_alarms <<< "$result"


# --- Print summary ---

function bold
{
  echo -e "$(tput bold)$*$(tput sgr0)"
}

function red
{
  echo -e "$(tput setaf 1)$*$(tput sgr0)"
}

function green
{
  echo -e "$(tput setaf 2)$*$(tput sgr0)"
}

function positive
{
  if [ ${1:0:2} -ge 0 ]
  then
    echo $(green $1)
  else
    echo $(red $1)
  fi
}

function negative
{
  if [ ${1:0:2} -le 0 ]
  then
    echo $(green $1)
  else
    echo $(red $1)
  fi
}

stmt_coverage=`bc <<<"scale=1; 100 * $sem_reach_stmt / $syn_reach_stmt"`
fun_coverage=`bc <<<"scale=1; 100 * $sem_reach_fun / $syn_reach_fun"`


printf "\n"
printf "$(bold '%12s') %s\n"                       "Target:"   "$target"
printf "$(bold '%12s') %'d kB\n"                   "Memory:"   "$memory"
printf "$(bold '%12s') %s s (%s from average)\n"   "Time:"     "$user_time" \
           "$(negative $diff_user_time%)"
printf "$(bold '%12s') %s (%s from min)\n"         "Warnings:" "$warnings" \
           "$(negative $diff_warnings)"
printf "$(bold '%12s') %s (%s from min)\n"         "Alarms:"   "$alarms" \
           "$(negative $diff_alarms)"
printf "$(bold '%12s') %s / %s stmt (%s%%)\n"   "Coverage:" \
           "$sem_reach_stmt" "$syn_reach_stmt" "$stmt_coverage"
printf "$(bold '%12s') %s / %s / %s functions (%s%%)\n\n" "" \
           "$sem_reach_fun" "$syn_reach_fun" "$total_fun" "$fun_coverage"
printf "\n"

