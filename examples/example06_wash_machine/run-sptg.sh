#!/bin/bash

# -e  Exit immediately if a command exits with a non-zero status.
set -e

# Absolute path of the current SAMPLE_DIR directory
SAMPLE_PATH="$( dirname "$(realpath "$0")" )"

# Basename of the current SAMPLE_DIR directory
SAMPLE_DIR="$( basename $SAMPLE_PATH )"

# Ensure that we are in the directory of this example
# for the main parent script ../run-all.sh
cd $SAMPLE_PATH

# We assume the SPTG executable path for all scripts, adjust if necessary
export SPTG_EXE=$( realpath -e $SAMPLE_PATH/../../bin/sptg.exe )
# SPTG_EXE=/c/_myDisk_/git/github/efm-symbex/org.eclipse.efm.symbex/Release/diversity.exe

# The selected Symbolic Execution Workflow
SPTG_SEW=$SAMPLE_PATH/workflow_4_testcase_generation.sew

#  We assume that the SPTG_SEW is configured with these output directory parameters.
SPTG_OUT=$SAMPLE_PATH/output
SPTG_OUT_PUML_MODEL=$SPTG_OUT/exemple06_wash_machine.puml
SPTG_OUT_PUML_TESTCASE=$SPTG_OUT/testcase.puml

echo "____________________________________________________________"
echo "| Starting SPTG on $SAMPLE_DIR..."
echo "| CWD = ~/$( realpath --relative-to=$HOME $( pwd ) )"
echo "| SPTG_EXE = ~/$( realpath --relative-to=$HOME $SPTG_EXE )"
echo "| SPTG_SEW = ~/$( realpath --relative-to=$HOME $SPTG_SEW )"
echo "| SPTG_OUT = ~/$( realpath --relative-to=$HOME $SPTG_OUT )"
echo "____________________________________________________________"

# Disable 'Exit immediately if a command exits with a non-zero status.''
# Because SPTG_EXE don't return zero if everything is OK !
set +e

# Execution of SPTG
# echo "$SPTG_EXE  $SPTG_SEW"
$SPTG_EXE  $SPTG_SEW

# get the exit code of the exection of SPTG_EXE
SPTG_EXE_RETURN_CODE=$?

# The expected exit code
SPTG_EXIT_COVERAGE_GOAL_ACHIEVED_CODE=101
SPTG_EXIT_COVERAGE_GOAL_UNACHIEVED_CODE=102

# Exit code checking ...
case $SPTG_EXE_RETURN_CODE in
    $SPTG_EXIT_COVERAGE_GOAL_ACHIEVED_CODE)
        set -e

        PLANTUML_JAR=$(realpath -m $SAMPLE_PATH/../../bin/plantuml.jar)
        if [ -f $PLANTUML_JAR ]
        then
            echo "____________________________________________________________"
            echo "| Generate SVG image for the input model ./$( realpath --relative-to=$SAMPLE_PATH $SPTG_OUT_PUML_MODEL )"
            java -jar $PLANTUML_JAR -tsvg  $SPTG_OUT_PUML_MODEL

            echo "| Generate SVG image for the output testcase ./$( realpath --relative-to=$SAMPLE_PATH $SPTG_OUT_PUML_TESTCASE )"
            java -jar $PLANTUML_JAR -tsvg  $SPTG_OUT_PUML_TESTCASE
        else
            echo "Download the 'plantuml.jar' file in the ./SPTG/bin from https://github.com/plantuml/plantuml/releases"
            
            GRAPHVIZ_DOT=/usr/bin/dot
            if [[ ! -f $GRAPHVIZ_DOT || ! -x $GRAPHVIZ_DOT ]]
            then
                PACKAGE_DIR=$( realpath -e $SAMPLE_PATH/../../packages )
                echo "Install Graphiz package from the directory '$( realpath --relative-to=$SAMPLE_PATH $PACKAGE_DIR)' !"
                echo "Go to '$( realpath --relative-to=$SAMPLE_PATH $PACKAGE_DIR)' and run 'sudo dpkg -i *.deb'"
            fi
        fi
        ;;
    $AVM_EXIT_COVERAGE_GOAL_UNACHIEVED_CODE)
         echo "** Correct the workflow configuration if need ! **"
        ;;
    *)
        echo "Unexpected exit code $SPTG_EXE_RETURN_CODE !"
        ;;
esac

# echo "____________________________________________________________"
echo "| End SPTG on $SAMPLE_DIR !"
echo "____________________________________________________________"


exit 0
