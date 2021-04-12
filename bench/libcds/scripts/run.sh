#!/bin/bash

if [ $# -lt 5 ]
then
  echo "usage: $0 home build results nthreads nth"
  exit 1
fi

home=$1
scripts=$home/scripts

build=$2
results=$3
nthreads=$4
nth=$5


# run stress tests

$scripts/run_stress.sh $home $build $results stress-queue-push-pop $nth
$scripts/run_stress.sh $home $build $results stress-stack $nth
$scripts/run_stress.sh $home $build $results stress-pqueue $nth
$scripts/run_stress.sh $home $build $results stress-map-insdel-string $nth
