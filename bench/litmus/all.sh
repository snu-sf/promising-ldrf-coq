#!/bin/bash

home=`dirname $0`
results=$home/results
build=$home/_build

$home/build.sh

rm -rf $results
mkdir -p $results

$home/run.sh $results $build 9 1 40000000
$home/run.sh $results $build 9 2 40000000
$home/run.sh $results $build 9 4 40000000
$home/run.sh $results $build 9 8 4000000
$home/run.sh $results $build 9 16 4000000
$home/run.sh $results $build 9 32 4000000
$home/run.sh $results $build 9 64 4000000
$home/run.sh $results $build 9 128 4000000
$home/run.sh $results $build 9 256 4000000

$home/run.sh $results $build 10 1 40000000
$home/run.sh $results $build 10 2 40000000
$home/run.sh $results $build 10 4 40000000
$home/run.sh $results $build 10 8 4000000
$home/run.sh $results $build 10 16 4000000
$home/run.sh $results $build 10 32 4000000
$home/run.sh $results $build 10 64 4000000
$home/run.sh $results $build 10 128 4000000
$home/run.sh $results $build 10 256 4000000

$home/run.sh $results $build 11 1 40000000
$home/run.sh $results $build 11 2 40000000
$home/run.sh $results $build 11 4 40000000
$home/run.sh $results $build 11 8 4000000
$home/run.sh $results $build 11 16 4000000
$home/run.sh $results $build 11 32 4000000
$home/run.sh $results $build 11 64 4000000
$home/run.sh $results $build 11 128 4000000
$home/run.sh $results $build 11 256 4000000

$home/run.sh $results $build 12 1 40000000
$home/run.sh $results $build 12 2 40000000
$home/run.sh $results $build 12 4 40000000
$home/run.sh $results $build 12 8 4000000
$home/run.sh $results $build 12 16 4000000
$home/run.sh $results $build 12 32 4000000
$home/run.sh $results $build 12 64 4000000
$home/run.sh $results $build 12 128 4000000
$home/run.sh $results $build 12 256 4000000
