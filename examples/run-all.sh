#!/bin/bash

# -e  Exit immediately if a command exits with a non-zero status.
set -e

# SAMPLE_MAIN_PATH=$(dirname $0)/
SAMPLE_MAIN_PATH="$( dirname "$( realpath "$0" )" )"

echo "____________________________________________________________"
echo "| Starting SPTG on all example directories in :"
echo "| $SAMPLE_MAIN_PATH"
echo "| Checking for the existence of the SPTG_EXE and the optional PLANTUML_JAR..."

# We assume the SPTG executable path for all scripts, adjust if necessary
SPTG_EXE=$( realpath -m $SAMPLE_MAIN_PATH/../bin/sptg.exe )

if [[ -f $SPTG_EXE && -x $SPTG_EXE ]]
then
    echo "| SPTG_EXE=$SPTG_EXE : OK !"
else
    echo "| SPTG_EXE=$SPTG_EXE : NOT FOUND !"
    echo "Compile the SPTG src and copy the Release/sptg.exe to the directory ./SPTG/bin"
    exit 1
fi

# We assume the PLANTUM JAR  path for all scripts, adjust if necessary
PLANTUML_JAR=$( realpath -m $SAMPLE_MAIN_PATH/../bin/plantuml.jar )
if [ -f $PLANTUML_JAR ]
then
    echo "| PLANTUML_JAR=$PLANTUML_JAR : OK !"
else
    echo "| PLANTUML_JAR=$PLANTUML_JAR : NOT FOUND !"
    echo "| Download it in the directory ./SPTG/bin from https://github.com/plantuml/plantuml/releases"
fi

# We assume the GRAPHVIZ_DOT executable required by PLANTUML_JAR is present, adjust if necessary
GRAPHVIZ_DOT=$( realpath -m $SAMPLE_MAIN_PATH/../bin/dot )
if [[ -f $GRAPHVIZ_DOT && -x $GRAPHVIZ_DOT ]]
then
    echo "| GRAPHVIZ_DOT=$GRAPHVIZ_DOT : OK !"
else
    echo "| GRAPHVIZ_DOT=$GRAPHVIZ_DOT : NOT FOUND !"
    echo "| Install it the your system with the command 'sudo apt install graphviz'"
fi

set +e

RUN_SAMPLE_ALL_SH=run-all.sh
RUN_SAMPLE_SPTG_SH=run-sptg.sh
# Run all Symbolic Exxecution Workflow of all examples
# that has the script $RUN_SAMPLE_SH
for sample in */; do
    if [ -d "$sample" ]; then
        if [ -f $SAMPLE_MAIN_PATH/$sample/$RUN_SAMPLE_ALL_SH ]
        then
            $SAMPLE_MAIN_PATH/$sample/$RUN_SAMPLE_ALL_SH
            # get the exit code of the execution of RUN_SAMPLE_ALL_SH
            RUN_SAMPLE_ALL_SH_RETURN_CODE=$?
            if [ ! $RUN_SAMPLE_ALL_SH_RETURN_CODE -eq 0 ]
            then
            	echo "Fail to run ./$sample/$RUN_SAMPLE_ALL_SH !"
            	echo "Exit code : $RUN_SAMPLE_ALL_SH_RETURN_CODE"
            	exit $RUN_SAMPLE_ALL_SH_RETURN_CODE
            fi
        elif [ -f $SAMPLE_MAIN_PATH/$sample/$RUN_SAMPLE_SPTG_SH ]
        then
            $SAMPLE_MAIN_PATH/$sample/$RUN_SAMPLE_SPTG_SH
            # get the exit code of the execution of RUN_SAMPLE_SPTG_SH
            RUN_SAMPLE_SPTG_SH_RETURN_CODE=$?
            if [ ! $RUN_SAMPLE_SPTG_SH_RETURN_CODE -eq 0 ]
            then
            	echo "Fail to run ./$sample/$RUN_SAMPLE_SPTG_SH !"
            	echo "Exit code : $RUN_SAMPLE_SPTG_SH_RETURN_CODE"
            	exit $RUN_SAMPLE_SPTG_SH_RETURN_CODE
            fi
        fi
    fi
done

echo "| End SPTG on all examples !"
echo "____________________________________________________________"

