#!/usr/bin/env bash

for file in `ls *.actor`;
  do
    printf "Running $file\n"
    krun -d ../src $file
done;
