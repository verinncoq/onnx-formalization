#!/bin/bash
set -e

apt update
apt install -y unzip build-essential expect

ORIGINAL_DIR=$(pwd)

mkdir -p ./tmp-install
cd ./tmp-install

curl -L -o platform.zip https://github.com/coq/platform/archive/refs/tags/2026.07.0.zip
unzip platform.zip

#Pre-answer questions in the script
export COQ_PLATFORM_RELEASE="f"
export COQ_PLATFORM_PACKAGE_PICK_FILE="package_picks/package-pick-9.1~2026.01.sh"
export COQ_PLATFORM_PARALLEL="p"
export COQ_PLATFORM_JOBS="4"
export COQ_PLATFORM_COMPCERT="n"
export COQ_PLATFORM_LARGE="e"
export COQ_PLATFORM_VST="n"

cd platform-2026.07.0
expect <<'EOF'
spawn ./coq_platform_make.sh
expect {
  "\[1/2/3/4\]" { send "1\r"; exp_continue }
  "- Do you want to continue?" { send "Y\r"; exp_continue }
  "Where should it be installed" { send "\r"; exp_continue }
  eof
}
EOF

eval $(opam env)

cd "$ORIGINAL_DIR"
rm -rf ./tmp-install
