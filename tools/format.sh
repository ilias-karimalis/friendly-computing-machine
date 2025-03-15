#!/bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
OSMOSIS_ROOT="${REPOSITORY_ROOT}/osmosis-model/src/"

# check if verusfmt is installed
if ! command -v verusfmt &> /dev/null
then
    cargo install verusfmt
fi

pushd ${OSMOSIS_ROOT} > /dev/null
find . -type f -name '*.rs' -exec verusfmt {} \;
popd > /dev/null
