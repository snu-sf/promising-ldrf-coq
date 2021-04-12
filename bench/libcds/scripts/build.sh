#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

export CC=/usr/bin/clang-10
export CXX=/usr/bin/clang++-10

home=$1
build=$2

cd $build
cmake -DCMAKE_BUILD_TYPE=RELEASE -DWITH_TESTS=ON $home
make -j64
cd $home
