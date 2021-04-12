#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
build=$2/test/stress/pqueue

cd $build

make -j push_pop.s
make -j __/main.s

cd $home
