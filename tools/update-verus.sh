#!/bin/bash

####################################################################################################
#
# Script to update the Verus git submodule and Rust toolchain.
#
####################################################################################################

set -eu

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)
VERUS_ROOT="${REPOSITORY_ROOT}/verus"
VERUS_VERSION="main"

echo "Repository root: ${REPOSITORY_ROOT}"
echo "Verus root:      ${VERUS_ROOT}"


# make sure we're in the repository root and initialize submodule
pushd ${REPOSITORY_ROOT} > /dev/null
git submodule init
git submodule update verus
popd > /dev/null

# go into the verus source directory and trigger toolchain installation
pushd ${VERUS_ROOT}/source > /dev/null

git fetch --all
git checkout ${VERUS_VERSION}
git pull

echo "Downloading Z3..."
./tools/get-z3.sh > /dev/null

echo "Verus version:   $(git rev-parse HEAD)"
rustc --version

popd > /dev/null


# make sure there are no staged changes
git reset HEAD
git add verus
git commit -sm "verus: update to version ${VERUS_VERSION}" || true


# rebuild verus
bash ${REPOSITORY_ROOT}/tools/build-verus.sh
