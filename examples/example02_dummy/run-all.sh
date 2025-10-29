#!/bin/bash

# -e  Exit immediately if a command exits with a non-zero status.
set -e

# Absolute path of the current SAMPLE_DIR directory
SAMPLE_PATH="$( dirname "$(realpath "$0")" )"

# Ensure that we are in the directory of this example
# for the main parent script ../run-all.sh
cd $SAMPLE_PATH

# Run all Symbolic Exxecutiohn Workflow for testpurpose of length 2
./run-sptg-h2.sh $@

# Run all Symbolic Exxecutiohn Workflow for testpurpose of length 5
./run-sptg-h5.sh $@
