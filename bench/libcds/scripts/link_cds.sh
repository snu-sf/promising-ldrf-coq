#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
src=$1/src
build=$2
link=$build/CMakeFiles/cds.dir/link.txt

cd $build

`sed 's/\.o/\.s/g' $link`

cd $home
