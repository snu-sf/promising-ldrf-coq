#!/bin/bash

if [ $# -lt 5 ]
then
  echo "usage: $0 home build results test nth"
  exit 1
fi

home=$1
bin=$2/bin
test=$4
results=$3/$test
out=$results/$5.txt

mkdir -p $results
cd $bin

touch $out
./$test > $out

cd $home
