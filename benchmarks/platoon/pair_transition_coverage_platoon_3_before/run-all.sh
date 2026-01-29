#!/bin/bash

# -e  Exit immediately if a command exits with a non-zero status.
set -e

SAMPLE_MAIN_PATH="$( dirname "$( realpath "$0" )" )"

BIN_PATH=$SAMPLE_MAIN_PATH/../../bin/

# Ensure that we are in the main directory of all examples
cd $SAMPLE_MAIN_PATH

echo "____________________________________________________________"
echo "| Starting SPTG on all example directories in :"
echo "| >>> $SAMPLE_MAIN_PATH"
echo "| Checking for the existence of the SPTG_EXE and the optional PLANTUML_JAR..."

# We assume the SPTG executable path for all scripts, adjust if necessary
SPTG_EXE=$( realpath -m $BIN_PATH/sptg.exe )

if [ -f $SPTG_EXE ]
then
	if [ -x $SPTG_EXE ]
	then
		echo "| SPTG_EXE=$SPTG_EXE : OK !"
	else
		echo "| SPTG_EXE=$SPTG_EXE : is found but not EXECUTABLE !"
		echo "We try chmod a+x $SPTG_EXE"

		chmod a+x $SPTG_EXE

		if [ -x $SPTG_EXE ]
		then
			echo "| SPTG_EXE=$SPTG_EXE : is now EXECUTABLE !"
		else
			echo "| Fail to set SPTG_EXE=$SPTG_EXE EXECUTABLE !"
			exit 1;
		fi
	fi
else
	echo "| SPTG_EXE=$SPTG_EXE : NOT FOUND !"
	echo "Compile the SPTG src and copy the Release/sptg.exe to the directory ./SPTG/bin"
	exit 1
fi

# We assume the PLANTUM JAR  path for all scripts, adjust if necessary
PLANTUML_JAR=$( realpath -m $BIN_PATH/plantuml.jar )
if [ -f $PLANTUML_JAR ]
then
	echo "| PLANTUML_JAR=$PLANTUML_JAR : OK !"
else
	echo "| PLANTUML_JAR=$PLANTUML_JAR : NOT FOUND !"
	echo "| Download it in the directory ./SPTG/bin from https://github.com/plantuml/plantuml/releases"
	exit 1;
fi

# We assume the GRAPHVIZ_DOT executable required by PLANTUML_JAR is present, adjust if necessary
GRAPHVIZ_DOT_EXE=dot
if [ -x "$(command -v $GRAPHVIZ_DOT_EXE)" ]
then
	echo "| GRAPHVIZ_DOT_EXE=$GRAPHVIZ_DOT_EXE : OK !"
else
	echo "| GRAPHVIZ_DOT_EXE=$GRAPHVIZ_DOT_EXE : NOT FOUND !"
	echo "| Install it the your system with the command 'sudo apt install graphviz'"
	exit 1;
fi


# We assume the solver Z3 executable required statistic collection is present, adjust if necessary
SOLVER_Z3_EXE=z3
if [ -x "$(command -v $SOLVER_Z3_EXE)" ]
then
	echo "| SOLVER_Z3_EXE=$SOLVER_Z3_EXE : OK !"
else
	echo "| SOLVER_Z3_EXE=$SOLVER_Z3_EXE : NOT FOUND !"
	echo "| Install it the your system with the command 'sudo apt install z3'"
	exit 1;
fi

SOLVER_Z3_CMD="$SOLVER_Z3_EXE -st"

EXTRACT_MAX_MEMORY=" | egrep -o ':max-memory +([0-9]+[.]?[0-9]*)' | egrep -o '([0-9]+[.]?[0-9]*)'"
EXTRACT_TOTAL_TIME=" | egrep -o ':total-time +([0-9]+[.]?[0-9]*)' | egrep -o '([0-9]+[.]?[0-9]*)'"

set +e

# Run all Symbolic Execution Workflow for all tescase generator
# that has the script $RUN_SAMPLE_SH
for testcase_sew in *.sew; do
	if [ -f $testcase_sew ]
	then
		SAMPLE_SEW_PATH="$(realpath "$testcase_sew")"

		SAMPLE_PATH="$( dirname $SAMPLE_SEW_PATH )"

		echo "____________________________________________________________"
		echo "____________________________________________________________"
		echo "SAMPLE_SEW --> $testcase_sew"
		echo "____________________________________________________________"

		TESTCASE_PATH=$SAMPLE_PATH/"$(basename "$testcase_sew" .sew)"
		echo "TESTCASE_PATH = $TESTCASE_PATH"

		echo "SPTG_EXE $SAMPLE_SEW_PATH"
		$SPTG_EXE $SAMPLE_SEW_PATH

		if [ -d $TESTCASE_PATH ]
		then
			BIGUEST_CONDITION_Z3_PATH=$TESTCASE_PATH/biguest_condition.z3

			echo "$SOLVER_Z3_CMD $testcase_sew --> biguest_condition.z3"

			BIGUEST_CONDITION_Z3_SIZE=$( stat --printf="%s" $BIGUEST_CONDITION_Z3_PATH )

			Z3_STATISTICS="$( $SOLVER_Z3_CMD $BIGUEST_CONDITION_Z3_PATH | egrep ":total-time|:max-memory" )"

			Z3_MAX_MEMORY="$( echo $Z3_STATISTICS | egrep -o ':max-memory +([0-9]+[.]?[0-9]*)' | egrep -o '([0-9]+[.]?[0-9]*)' )"
			echo "Z3_MAX_MEMORY = $Z3_MAX_MEMORY"

			Z3_TOTAL_TIME="$( echo $Z3_STATISTICS | egrep -o ':total-time +([0-9]+[.]?[0-9]*)' | egrep -o '([0-9]+[.]?[0-9]*)' )"
			echo "Z3_TOTAL_TIME = $Z3_TOTAL_TIME"

			for model_puml in $*.puml; do
				if [ -f $model_puml ]
				then
					echo "_____________________TESTCASE_PATH/_______________________________________"
					echo "| Generate SVG image for the puml model ./$( realpath --relative-to=$SAMPLE_PATH $model_puml)"
					java -jar $PLANTUML_JAR -tsvg  $model_puml
				fi
			done
		fi
	fi
done

echo "| End SPTG on all examples !"
echo "____________________________________________________________"
