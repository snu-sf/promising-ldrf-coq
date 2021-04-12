#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
src=$1/test/stress/framework
build=$2/test/stress

cd $build

for file in `ls $src/*.cpp`; do
  name=`basename $file`
  make -j framework/$name.s
done

cd $home
