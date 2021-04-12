#!/bin/bash

rootdir=$1

rm -f $rootdir/stat.csv

rm -f parse
g++ -std=c++17 -O3 parse.cpp -o parse

rm -f stat
g++ -std=c++17 -O3 stat.cpp -o stat

rm -f merge
g++ -std=c++17 -O3 merge.cpp -o merge

for dir in `ls $rootdir`; do
  dir=$rootdir/$dir
  outdir=$dir/out
  rm -rf $outdir
  mkdir -p $outdir

  for file in `cd $dir; ls *.txt`; do
    ./parse $dir $file $outdir $2 $3
  done
  
  ./merge $dir
  for file in `ls $outdir/*.csv`; do
    ./merge $dir $file
  done
done

./stat $rootdir $2 $3
