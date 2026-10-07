#!/bin/bash 

# Temporary script for converting LLZK to PCL.
# USAGE: scripts/llzk2pcl.sh <llzk file> <pcl file>

if [[ $# < 2 ]] ; then
  >&2 echo "USAGE: $0 <llzk source> <pcl dest>"
  exit 1
fi

opt="$LLZK_SYS_10_PREFIX/bin/llzk-opt"
translate="$LLZK_SYS_10_PREFIX/bin/llzk-translate"
llzk=$1 
pcl=$2

if ! [ -f $opt ] ; then 
  echo "llzk-opt tool not found"
  exit 1 
fi
if ! [ -f $translate ] ; then 
  echo "llzk-translate tool not found"
  exit 1 
fi 

echo 'Src: ' $llzk 
echo Dest: $pcl

$opt $llzk \
  --llzk-to-pcl \
  --cse \
  --canonicalize \
  --emit-bytecode | $translate $tmp --pcl-to-lisp -o $pcl
