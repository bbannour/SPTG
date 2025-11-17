#!/bin/bash

# -e  Exit immediately if a command exits with a non-zero status.
set -e

# Absolute path of the current SAMPLE_DIR directory
SAMPLE_PATH="$( dirname "$(realpath "$0")" )"

# Ensure that we are in the directory of this example
# for the main parent script ../run-all.sh
cd $SAMPLE_PATH

# Run all Symbolic Execution Workflow for testpurpose of length 2
if [ ! -x ./run-sptg-h2.sh ]
then
	chmod a+x ./run-sptg-h2.sh
fi
./run-sptg-h2.sh $@
RUN_SAMPLE_H2_SH_RETURN_CODE=$?
if [ ! $RUN_SAMPLE_H2_SH_RETURN_CODE -eq 0 ]
then
	echo "Fail to run ./$sample/$RUN_SAMPLE_ALL_SH !"
	echo "Exit code : $RUN_SAMPLE_H2_SH_RETURN_CODE"
fi

# Run all Symbolic Execution Workflow for testpurpose of length 5
if [ ! -x ./run-sptg-h5.sh ]
then
	chmod a+x ./run-sptg-h5.sh
fi
./run-sptg-h5.sh $@
RUN_SAMPLE_H5_SH_RETURN_CODE=$?
if [ ! $RUN_SAMPLE_H5_SH_RETURN_CODE -eq 0 ]
then
	echo "Fail to run ./$sample/$RUN_SAMPLE_ALL_SH !"
	echo "Exit code : $RUN_SAMPLE_H5_SH_RETURN_CODE"
fi

echo "| End SPTG on all examples on $SAMPLE_DIR !"
echo "____________________________________________________________"
