#!/bin/sh


dune build

SCRIPT_DIR=$(dirname "$0")
"$SCRIPT_DIR/post-build.sh"
