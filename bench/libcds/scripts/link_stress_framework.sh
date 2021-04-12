#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home"
  exit 1
fi

home=$1
build=$2/test/stress
link=$build/CMakeFiles/stress-framework.dir/link.txt

cd $build

`sed 's/\.o/\.s/g' $link`

cd $home
