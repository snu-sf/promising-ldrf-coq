#!/bin/bash

if [ $# -lt 2 ]
then
  echo "usage: $0 home build"
  exit 1
fi

home=$1
scripts=$home/scripts
build=$2


# link

$scripts/link_cds.sh $home $build
$scripts/link_stress_framework.sh $home $build
$scripts/link_stress_queue_push_pop.sh $home $build
$scripts/link_stress_stack.sh $home $build
$scripts/link_stress_pqueue.sh $home $build
$scripts/link_stress_map_insdel_string.sh $home $build
