#!/bin/bash
set -e

ORIGINAL_DIR=$(pwd)

mkdir -p ./tmp-install
cd ./tmp-install

curl -L -o platform.zip https://github.com/coq/platform/archive/refs/tags/2026.07.0.zip
unzip platform.zip

cd platform-2026.07.0
./coq_platform_make.sh

eval $(opam env)

cd "$ORIGINAL_DIR"
rm -rf ./tmp-install
