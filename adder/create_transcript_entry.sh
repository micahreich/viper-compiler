#!/bin/bash

file="$1"
filename=$(basename "$file")

echo -e "\n---------- .snek file ($file) ----------"
cat "test/$filename.snek"
echo -e "\n---------- make command ($file) ----------"
make "test/$filename.run"
echo -e "\n---------- .s file ($file) ----------"
cat "test/$filename.s"
echo -e "\n---------- program out ($file) ----------"
./test/$filename.run