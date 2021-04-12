#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
scripts=$home/scripts
build=$2


# emit assemblies

find . -name "*.s" | xargs rm -f
$scripts/emit_cds.sh $home $build
$scripts/emit_stress_framework.sh $home $build
$scripts/emit_stress_queue_push_pop.sh $home $build
$scripts/emit_stress_stack.sh $home $build
$scripts/emit_stress_pqueue.sh $home $build
$scripts/emit_stress_map_insdel_string.sh $home $build
