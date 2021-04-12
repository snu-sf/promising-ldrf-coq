#!/bin/bash

dir=$1
runs=$2
discarded=$3

outdir=$dir/out
rm -rf $outdir
mkdir -p $outdir

kinds=( "9" "10" "11" "12" )

rm -f $dir/stat.csv

rm -f parse_litmus
g++ -std=c++17 -O3 parse_litmus.cpp -o parse_litmus

for kind in ${kinds[@]}; do
    ./parse_litmus $dir $kind 1 256 $runs $discarded
done
