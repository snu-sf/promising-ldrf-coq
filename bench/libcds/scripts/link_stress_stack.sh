#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
build=$2/test/stress/stack
link=$build/CMakeFiles/stress-stack.dir/link.txt

cd $build

`sed 's/\.o/\.s/g' $link`

cd $home
