#!/usr/bin/env bash
set -euo pipefail

# get the directory the file is in
source_dir() {
    local SOURCE_DIR
    SOURCE_DIR=$(readlink -f "${BASH_SOURCE[0]}")
    dirname "$SOURCE_DIR"
}

# find a jar in java's boot classpath
find_bootcp_jar() {
    java -XshowSettings:properties -version 2>&1 \
        | grep "${1}.jar" \
        | head -1 \
        | awk '{print $NF}'
}

export CLASSPATH

cd "$(source_dir)"
CLASSPATH=$(find_bootcp_jar rt)

./main.byte "$@"
