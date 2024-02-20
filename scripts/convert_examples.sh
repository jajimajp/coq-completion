#!/bin/sh
(cd $EXAMPLE && find .) | grep .trs | sed -e 's/.trs//g' -e 's/\.\///g' | xargs -I{} sh -c "bin/a.out $EXAMPLE/{}.trs > ./examples/generated/{}.v"