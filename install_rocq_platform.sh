#!/bin/bash
set -e

sudo apt update
sudo apt install -y unzip build-essential expect

ORIGINAL_DIR=$(pwd)

mkdir -p ./tmp-install
cd ./tmp-install

curl -L -o platform.zip https://github.com/coq/platform/archive/refs/tags/2026.07.0.zip
unzip platform.zip

cd platform-2026.07.0
expect <<'EOF'
spawn ./coq_platform_make.sh
expect {
  "Install full" { send "b\r"; exp_continue }
  "Select package list" { send "1\r"; exp_continue }
  "Build opam packages parallel" { send "p\r"; exp_continue }
  "Number of parallel make jobs" { send "4\r"; exp_continue }
  "Install non open source SW CompCert" { send "n\r"; exp_continue }
  "Include (i) exclude (e) or select (s) large packages" { send "e\r"; exp_continue }
  "Install VST" { send "n\r"; exp_continue }
  "\[1/2/3/4\]" { send "1\r"; exp_continue }
  -glob "*Do you want to continue?*" { send "Y\r"; exp_continue }
  "Where should it be installed" { send "\r"; exp_continue }
  eof
}
EOF

eval $(opam env)

cd "$ORIGINAL_DIR"
rm -rf ./tmp-install
