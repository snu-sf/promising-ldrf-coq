#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
build=$2/test/stress/map/insdel_string
link=$build/CMakeFiles/stress-map-insdel-string.dir/link.txt

cd $build

`sed 's/\.o/\.s/g' $link`

cd $home
