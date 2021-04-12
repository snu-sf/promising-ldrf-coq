#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
build=$2/test/stress/map/insdel_string

cd $build

make -j map_insdel_string.s
make -j map_insdel_string_bronsonavltree.s
make -j map_insdel_string_cuckoo.s
make -j map_insdel_string_ellentree.s
make -j __/__/main.s

cd $home
