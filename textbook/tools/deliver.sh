#!/bin/bash
# copy out/<stem>.pdf onto the previously delivered file name and print its path
cd "$(dirname "$0")/.."
O=/mnt/user-data/outputs/textbook
case "$1" in intA) pat=InterludeA_;; intB) pat=InterludeB_;; front) pat=Ch00_;; *) pat="Ch${1#ch}_";; esac
f=$(ls $O | grep "^$pat" | head -1)
cp "out/$1.pdf" "$O/$f" && echo "$O/$f"
