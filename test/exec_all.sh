#!/usr/bin/env bash

for file in `ls *.actor`;
  do
    printf "Running $file\n"
    krun -d ../src $file > temp.xml
    xmllint --format temp.xml | tail -n +2
    printf "\n"
    rm temp.xml
done;
