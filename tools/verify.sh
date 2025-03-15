#!/bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"
OSMOSIS_ROOT="${REPOSITORY_ROOT}/osmosis-model/src/lib.rs"

# check if verus has been initialized
if [[ ! -f "${VERUS_ROOT}/source/target-verus/release/verus" ]]; then
    echo 'Verus not initialized. Execute `tools/build-verus.sh` first.'
    exit 1
fi

# now verify the main osmosis model
pushd ${VERUS_ROOT}/source > /dev/null
echo "Verifying '${OSMOSIS_ROOT}' ... "
./target-verus/release/verus --crate-type=lib --expand-errors $@ ${OSMOSIS_ROOT}
echo "Verification done."
popd > /dev/null
