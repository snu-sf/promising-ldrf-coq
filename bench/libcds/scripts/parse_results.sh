#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 scripts results"
  exit 1
fi

scripts=$1
results=$2

for dir in `ls $results`; do
  touch $results/$dir.txt
  for file in `ls $results/$dir`; do
    python3 $scripts/parse_result.py $results/$dir/$file >> $results/$dir.txt
  done
done
