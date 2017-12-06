#!/usr/bin/env bash

krun -d ../src $1 > temp.xml
xmllint --format temp.xml | tail -n +2
rm temp.xml
