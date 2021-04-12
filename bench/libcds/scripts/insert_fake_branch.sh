#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
build=$2
dir=`dirname $0`
insert=$1/scripts/insert_fake_branch.py

cd $build

file_num=0

for file in `find . -name "*.s"`; do
  python3 $insert $file tmp.s $file_num
  rm -f tmp.s
  file_num=$((file_num + 1))
done

cd $home
