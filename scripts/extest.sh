#!/bin/bash

l=$(find examples/generated | grep \.v$)
for f in $l; do
  timeout 20 coqc $f >/dev/null 2>/dev/null
  if [ $? -eq 0 ]; then
    echo "$f : OK"
  else
    echo "$f : FAIL"
  fi
done
