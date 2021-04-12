#!/bin/bash

home=`dirname $0`
build=$home/_build
src=$home/src
CC=clang++-10
flag="-std=c++11 -O3"

rm -rf $build
mkdir $build

$CC $flag -c $src/incr.cpp -o $build/incr.o
$CC $flag -c $src/main.cpp -o $build/main.o
$CC $flag -lpthread $build/incr.o $build/main.o -o $build/main

$CC $flag -S $src/incr.cpp -o $build/incr.s

python3 $home/insert_fake_branch.py $build/incr.s $build/incr.fake.s 0
$CC $flag -lpthread $build/incr.fake.s $build/main.o -o $build/main.fake

python3 $home/insert_fake_branch_cmp.py $build/incr.s $build/incr.cmp.s 0
$CC $flag -lpthread $build/incr.cmp.s $build/main.o -o $build/main.cmp
