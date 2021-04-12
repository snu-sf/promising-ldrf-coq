#!/bin/bash

if [ $# -lt 1 ]
then
  echo "usage: $0 home"
  exit 1
fi

home=`pwd`/$1
scripts=$home/scripts
build_ref=$home/_build_ref
build_fake=$home/_build_fake
build_cmp=$home/_build_cmp
# build_nop=$home/_build_nop

results_32=$home/results_32
results_32_ref=$home/results_32/ref
results_32_fake=$home/results_32/fake
results_32_cmp=$home/results_32/cmp
# results_32_nop=$home/results_32/nop

results_128=$home/results_128
results_128_ref=$home/results_128/ref
results_128_fake=$home/results_128/fake
results_128_cmp=$home/results_128/cmp
# results_128_nop=$home/results_128/nop


# build

rm -rf $build_ref
rm -rf $build_fake
rm -rf $build_cmp
# rm -rf $build_nop

mkdir -p $build_ref
mkdir -p $build_fake
mkdir -p $build_cmp
# mkdir -p $build_nop

$scripts/build.sh $home $build_ref

$scripts/build.sh $home $build_fake
$scripts/emit.sh $home $build_fake
$scripts/insert_fake_branch.sh $home $build_fake
$scripts/link.sh $home $build_fake

$scripts/build.sh $home $build_cmp
$scripts/emit.sh $home $build_cmp
$scripts/insert_fake_branch_cmp.sh $home $build_cmp
$scripts/link.sh $home $build_cmp

# $scripts/build.sh $home $build_nop
# $scripts/emit.sh $home $build_nop
# $scripts/insert_nop.sh $home $build_nop
# $scripts/link.sh $home $build_nop


# run 32 threads tests

echo "==================================="
echo "running tests in 32 threads..."
echo "-----------------------------------"

rm -rf $results_32
mkdir -p $results_32
mkdir -p $results_32_ref
mkdir -p $results_32_fake
mkdir -p $results_32_cmp
# mkdir -p $results_32_nop

cp -f $scripts/conf/test-32.conf $build_ref/bin/test.conf
cp -f $scripts/conf/test-32.conf $build_fake/bin/test.conf
cp -f $scripts/conf/test-32.conf $build_cmp/bin/test.conf
# cp -f $scripts/conf/test-32.conf $build_nop/bin/test.conf

for i in {1..10}
do
  echo "running $i-th test..."
  $scripts/run.sh $home $build_ref $results_32_ref 32 $i
  $scripts/run.sh $home $build_fake $results_32_fake 32 $i
  $scripts/run.sh $home $build_cmp $results_32_cmp 32 $i
#   $scripts/run.sh $home $build_nop $results_32_nop 32 $i
done

$scripts/parse_results.sh $scripts $results_32_ref
$scripts/parse_results.sh $scripts $results_32_fake
$scripts/parse_results.sh $scripts $results_32_cmp
# $scripts/parse_results.sh $scripts $results_32_nop


# run 128 threads tests

echo "==================================="
echo "running tests in 128 threads..."
echo "-----------------------------------"

rm -rf $results_128
mkdir -p $results_128
mkdir -p $results_128_ref
mkdir -p $results_128_fake
mkdir -p $results_128_cmp
# mkdir -p $results_128_nop

cp -f $scripts/conf/test-128.conf $build_ref/bin/test.conf
cp -f $scripts/conf/test-128.conf $build_fake/bin/test.conf
cp -f $scripts/conf/test-128.conf $build_cmp/bin/test.conf
# cp -f $scripts/conf/test-128.conf $build_nop/bin/test.conf

for i in {1..360}
do
  echo "running $i-th test..."
  $scripts/run.sh $home $build_ref $results_128_ref 128 $i
  $scripts/run.sh $home $build_fake $results_128_fake 128 $i
  $scripts/run.sh $home $build_cmp $results_128_cmp 128 $i
#   $scripts/run.sh $home $build_nop $results_128_nop 128 $i
done

$scripts/parse_results.sh $scripts $results_128_ref
$scripts/parse_results.sh $scripts $results_128_fake
$scripts/parse_results.sh $scripts $results_128_cmp
# $scripts/parse_results.sh $scripts $results_128_nop
