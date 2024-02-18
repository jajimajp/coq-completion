#!/bin/sh

# `dune build` によって生成される META.auto-eq-prover-coq について、下記の問題を強制的に修正する。
# - トップレベルに directory の指定がないために、Coq で読み込んだ際にエラーが出る。 

FILE=_build/default/META.coq-completion

chmod +w $FILE
sed -i '' -e '/^directory = .*$/d' $FILE
echo '\ndirectory = "."' >> $FILE
sed -i '' -e '/^$/d' $FILE
chmod -w $FILE
