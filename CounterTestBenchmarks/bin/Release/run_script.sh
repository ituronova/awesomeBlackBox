#!/bin/bash

input="C:\Users\42073\Desktop\Code\Automata\regexes\test-simp"

file=path/of/file/location/filename.txt

while IFS= read -r varname; do
    printf '%s\n' "$varname"
done < "$input"

#./CounterAutomataBench --both "[a-q][^u-z]{13}x" "C:\Users\42073\Desktop\Automata\pg3200.txt"
