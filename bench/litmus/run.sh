#!/bin/bash

if [ $# -lt 5 ]
then
  echo "usage: $0 results build kind n_threads n_op"
  exit 1
fi

home=`dirname $0`
results=$1
build=$2
kind=$3
n_threads=$4
n_op=$5

out=$results/main-$kind-$n_threads-$n_op.txt
out_fake=$results/main.fake-$kind-$n_threads-$n_op.txt
out_cmp=$results/main.cmp-$kind-$n_threads-$n_op.txt

rm -f $out $out_fake $out_cmp
touch $out $out_fake $out_cmp
echo "running (kind:$kind, n_threads:$n_threads, n_op:$n_op)..."

for i in {1..360}
do
  $home/_build/main.cmp $kind $n_threads $n_op >> $out_cmp
  $home/_build/main $kind $n_threads $n_op >> $out
  $home/_build/main.fake $kind $n_threads $n_op >> $out_fake
done
