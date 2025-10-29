/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CommonExecutionGraphSerializer.h"

#include <computer/PathConditionProcessor.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>
#include <fml/runtime/TableOfData.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerUnitManager.h>

#include <boost/format.hpp>


namespace sep
{

/**
 * EXECUTION CONTEXT NODE
 * %1% --> node#id
 * %2% --> node#label
 * %3% --> node#css
 * %4% --> node#data
 * %5% --> node#info
 * %6% --> node#trace#run
 * %7% --> node#trace#io
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_PATTERN = "\nEC%1% [%2%%3%\n]%4%";

/**
 * EXECUTION CONTEXT NODE LABEL
 * %1% --> node#id
 * %2% --> node#header
 * %3% --> node#data
 * %4% --> node#info
 * %5% --> node#trace#run
 * %6% --> node#trace#io
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_LABEL_PATTERN = "\n\tlabel=\"%2%%4%\"";

/**
 * EXECUTION CONTEXT NODE CSS ATTRIBUTES
 * %1% --> node#id
 * %2% --> node#color
 * %3% --> node#shape
 * %4% --> node#style
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_CSS_ATTRIBUTES =
		"\n\tcolor=%2%\n\tshape=%3%\n\tstyle=%4%";

// CSS PROFILE: COLOR / SHAPE / STYLE

// NODE DEFAULT CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_CSS_COLOR = "lightblue";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_CSS_SHAPE = "box"; //"ellipse";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_CSS_STYLE = "rounded"; //"filled";

// NODE PASSED CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_COLOR = "yellow";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE FAILED CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_COLOR = "orange";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_SHAPE = "doubleoctagon";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE INCONCLUSIVE CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_COLOR = "orange";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ABORTED CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_COLOR = "red";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_SHAPE = "octagon";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE TIMEOUT CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_COLOR = "orange";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_SHAPE = "octagon";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE WARNING CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_COLOR = "orange";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ERROR CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_COLOR = "red";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ALERT CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_COLOR = "red";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE EXIT CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_COLOR = "yellow";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE REDUNDANCY_SOURCE CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_COLOR = "green";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_SHAPE = "cds";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE REDUNDANCY_TARGET CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_COLOR = "greenyellow";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_SHAPE = "septagon";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;


// PATH PASSED CSS
const std::string & CommonExecutionGraphSerializer::
CONTEXT_PATH_PASSED_CSS_COLOR = "lawngreen";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_PATH_PASSED_CSS_SHAPE = "tripleoctagon";

const std::string & CommonExecutionGraphSerializer::
CONTEXT_PATH_PASSED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;


/**
 * EXECUTION CONTEXT EDGE
 * %1% --> node#source#id
 * %2% --> node#target#id
 * %3% --> node#target#data
 * %4% --> node#target#info
 * %5% --> node#target#fired
 * %6% --> node#target#trace
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_EDGE_PATTERN = "\nEC%1% -> EC%2% [\n\tlabel=\"%5%%6%\"\n]";

/**
 * EXECUTION CONTEXT HEADER
 * %1% --> ec#id
 * %2% --> ec#eval
 * %3% --> ec#hight
 * %4% --> ec#width
 * %5% --> ec#weight
 * %6% --> statemachine configuration i.e. lifelines state identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_HEADER_PATTERN = "EC#%1%<Ev:%2%>\\n%6%";

/**
 * EXECUTION DATA
 * %1% --> ec#id
 * %2% --> ec#assign
 * %3% --> ec#path#condition
 * %4% --> ec#path#timed#condition
 * %5% --> ec#node#condition
 * %6% --> ec#node#timed#condition
 * %7% --> ec#node#buffer
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_DATA_PATTERN = "\nEC%1% -> ED%1%\nED%1% "
		"[\n\tlabel=\"%3%%4%%5%%6%%2%%7%\"\n\tshape=box\n]";

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution info
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_INFO_PATTERN = "\n%2%";
//		"\nEC%1% -> EI%1%\nEI%1% [\n\tlabel=\"%2%\""
//		"\n\tshape=octagon\n\tcolor=yellow\n\tstyle=filled\n]";

/**
 * EXECUTION CONTEXT FIRED
 * %1% --> node#id
 * %2% --> execution fired
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_FIRED_PATTERN = "%2%";

/**
 * EXECUTION CONTEXT TRACE
 * %1% --> node#id
 * %2% --> execution trace
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_TRACE_PATTERN = "%2%";

/**
 * EXECUTION CONTEXT FLAGS
 * %1% --> node#id
 * %2% --> flags
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_FLAGS_PATTERN = "%1%: %2%";

/**
 * INFO
 * %1% --> info id
 * %2% --> info data
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_INFO_PATTERN = "%1%: %2%";


const std::string & CommonExecutionGraphSerializer::
STANDARD_INFO_PATTERN = "%2%";

/**
 * CONDITION
 *  %1% --> condition
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_PATH_CONDITION_PATTERN = "" /*"PC: %1%"*/;

const std::string & CommonExecutionGraphSerializer::
DEFAULT_PATH_TIMED_CONDITION_PATTERN = "" /*"PtC: %1%"*/;

const std::string & CommonExecutionGraphSerializer::
DEFAULT_NODE_CONDITION_PATTERN = "" /*"NC: %1%"*/;

const std::string & CommonExecutionGraphSerializer::
DEFAULT_NODE_TIMED_CONDITION_PATTERN = ""/*"NtC: %1%"*/;

/**
 * ASSIGN BUFFER
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> buffer identifier
 * %4% --> value
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_ASSIGN_BUFFER_PATTERN = "%2%:%3% = %4%";

/**
 * ASSIGN VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> (variable | buffer) identifier
 * %4% --> value
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_ASSIGN_VARIABLE_PATTERN = "%2%:%3% = %4%";

/**
 * NEWFRESH VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_NEWFRESH_PATTERN = "newfresh %2%->%3%( %4% )";

/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> ( port | signal ) identifier
 * %4% --> value
 * %5% --> machine sender   identifier name
 * %6% --> machine receiver identifier name
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_INPUT_PATTERN = "%2%->%3% ? %4%";

const std::string & CommonExecutionGraphSerializer::
DEFAULT_OUTPUT_PATTERN = "%2%->%3% ! %4%";


const std::string & CommonExecutionGraphSerializer::
DEFAULT_INPUT_ENV_PATTERN = "env => %2%->%3% ? %4%";

const std::string & CommonExecutionGraphSerializer::
DEFAULT_OUTPUT_ENV_PATTERN = "env <= %2%->%3% ! %4%";


const std::string & CommonExecutionGraphSerializer::
DEFAULT_INPUT_RDV_PATTERN = "\tinput#rdv  %2%->%3%%4%\n";

const std::string & CommonExecutionGraphSerializer::
DEFAULT_OUTPUT_RDV_PATTERN = "\toutput#rdv %2%->%3%%4%\n";


/**
 * LIFELINE STATE IDENTIFIER
 * %1% --> lifeline runtime pid
 * %2% --> lifeline identifier
 * %3% --> state runtime pid
 * %4% --> state identifier
 * %5% --> state kind
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_LIFELINE_STATE_PATTERN = "%2%:%4%";

/**
 * STATE KIND IDENTIFIER
 * %1% --> initial | final
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_STATE_KIND_PATTERN = "%1%";

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> machine identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_MACHINE_PATTERN = "%3%";

const std::string & CommonExecutionGraphSerializer::
DEFAULT_STATEMACHINE_PATTERN = "%3%";

const std::string & CommonExecutionGraphSerializer::
DEFAULT_STATE_PATTERN = "%3%";

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> transition identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_TRANSITION_PATTERN = "%2%->%3%";

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_ROUTINE_PATTERN = "%2%->%3%";

/**
 * VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_VARIABLE_PATTERN = "%1%->%3%";


/**
 * BUFFER
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> buffer identifier
 */
const std::string & CommonExecutionGraphSerializer::
DEFAULT_BUFFER_PATTERN = "%1%->%3%";





/*******************************************************************************
serializer += CommonExecutionGraphSerializer <name-id> "<description>" {
	// ...

@property:

@trace:

@format:

@vfs:
	file = "<save-file-path>"
}
*******************************************************************************/

/**
prototype processor::serializer#graph "serialize graph" as CommonExecutionGraphSerializer is
section PROPERTY
	@info#selection = 'ALL';   		// ALL | MODIFIED
	@data#selection = 'ALL';   		// ALL | MODIFIED
endsection PROPERTY

section FORMAT
	@line#wrap#width = 42;
	@line#wrap#separator = "\\l";

	// %1% --> graph name#id
	@header = "digraph model_%1% {\n";
	@end    = "\n}";

	// %1% --> node#id
	// %2% --> node#label
	// %3% --> node#css
	// %4% --> node#data
	// %5% --> node#info
	// %6% --> node#trace#run
	// %7% --> node#trace#io
	@node = "\nEC%1% [%2%%3%\n]%5%%4%";

	// %1% --> node#id
	// %2% --> node#header
	// %3% --> node#data
	// %4% --> node#info
	// %5% --> node#trace#run
	// %6% --> node#trace#io
	@node#label = "\n\tlabel=\"%2%\"";

	// %1% --> node#id
	// %2% --> node#color
	// %3% --> node#shape
	// %4% --> node#style
	@node#css = "\n\tcolor=%2%\n\tshape=%3%\n\tstyle=%4%";

	// %1% --> node#source#id
	// %2% --> node#target#id
	// %3% --> node#target#data
	// %4% --> node#target#info
	// %5% --> node#target#fired
	// %6% --> node#target#trace
	@edge = "\nEC%1% -> EC%2% [\n\tlabel=\"%5%%6%\"\n]";

	// %1% --> ec#id
	// %2% --> ec#eval
	// %3% --> ec#hight
	// %4% --> ec#width
	// %5% --> ec#weight
	// %6% --> statemachine configuration i.e. lifelines state identifier
	@node#header = "EC#%1%<Ev:%2%>\n%6%";

	// %1% --> ec#id
	// %2% --> ec#assign
	// %3% --> ec#path#condition
	// %4% --> ec#path#timed#condition
	// %5% --> ec#node#condition
	// %6% --> ec#node#timed#condition
 	// %7% --> ec#node#buffer
	@node#data = "\nEC%1% -> ED%1%\nED%1% [\n\tlabel=\"%3%%4%%5%%6%%2%%7%\"\n\tshape=box\n]";

	// %1% --> node#id
	// %2% --> execution info
	@node#info = "\nEC%1% -> EI%1%\nEI%1% [\n\tlabel=\"%2%\"\n\tshape=box\n\tcolor=yellow\n\tstyle=filled\n]";

	// %1% --> node#id
	// %2% --> execution fired
	@node#trace#run = "%2%";

	// %1% --> node#id
	// %2% --> execution trace
	@node#trace#io = "%2%";


	// %1% --> info id
	// %2% --> info data
	@info = "%2%";

	// %1% --> condition
	@path#condition = "PC: %1%";
	@path#timed#condition = "PtC: %1%";
	@node#condition = "NC: %1%";
	@node#timed#condition = "NtC: %1%";

	// %1% --> machine runtime pid
	// %2% --> machine identifier name
	// %3% --> port | signal | variable | machine | transition | routine
	// %4% --> value
	@assign     = "%2%:%3%=%4%";

	@newfresh   = "newfresh(%1%:%3%) <- %4%";

	@machine    = "";
	@machine    = "run %1%:%3%";

	@transition = "fired %3%";
	@routine    = "invoke %2%:%3%";

	@input  = "%3% ? %4%";
	@input  = "%1%->%3% ? %4%";

	@input#env = "env => %1%->%3% ? %4%";

	@output = "%3% ! %4%";
	@output = "%1%->%3% ! %4%";

	@output#env = "env <= %1%->%3% ! %4%";
endsection FORMAT
section TRACE
	@machine = "[*]";

	@state = "[*]";
	@tatemachine = "[*]";

	@transition = "[*]";

	@routine = "[*]";

	@com = "[*]";

	@input  = "[*]";
	@output = "[*]";

	@newfresh = "[*]";
	@variable = "[*]";
endsection TRACE
section VFS
	@file = "graph.gv";
endsection VFS
endprototype


serializer#model#graphviz model2graphiz {
	vfs [
		file = "game_graph.gv"
	] // end vfs
}
serializer#symbex#graphviz symbex2graphiz {
	property [
		info#selection = 'ALL'
		data#selection = 'MODIFIED'
	] // end property
	format [
		lifeline#state = "%2%:%4%"
		path#condition = "PC: %1%"
		path#timed#condition = "PtC: %1%"
		node#condition = ""
		node#timed#condition = ""
		assign = "%3%=%4%"
		newfresh = "newfresh(%2%:%3%) <- %4%"
		input#env = "INPUT %2%:%3%%4%"
		input#rdv = "input %2%:%3%%4%"
		input = "input %2%:%3%%4%"
		output#env = "OUTPUT %2%:%3%%4%"
		output#rdv = "output %2%:%3%%4%"
		output = "output %2%:%3%%4%"
		routine = "invoke %2%:%3%"
		transition = "fired transition %3%"
		machine = "run %2%:%3%"
	] // end format
	css [
		node#color = 'lightblue'
		node#shape = 'ellipse'
		node#style = 'filled'
		node#passed#color = 'yellow'
		node#passed#shape = 'tripleoctagon'
		node#passed#style = 'filled'
		node#failed#color = 'red'
		node#failed#shape = 'doubleoctagon'
		node#failed#style = 'filled'
		node#inconclusive#color = 'orange'
		node#inconclusive#shape = 'octagon'
		node#inconclusive#style = 'filled'
		node#aborted#color = 'red'
		node#aborted#shape = 'octagon'
		node#aborted#style = 'filled'
		node#warning#color = 'orange'
		node#warning#shape = 'ellipse'
		node#warning#style = 'filled'
		node#error#color = 'red'
		node#error#shape = 'ellipse'
		node#error#style = 'filled'
		node#alert#color = 'red'
		node#alert#shape = 'ellipse'
		node#alert#style = 'filled'
		node#exit#color = 'orange'
		node#exit#shape = 'tripleoctagon'
		node#exit#style = 'filled'
		node#redundancy#source#color = 'green'
		node#redundancy#source#shape = 'cds'
		node#redundancy#source#style = 'filled'
		node#redundancy#target#color = 'greenyellow'
		node#redundancy#target#shape = 'septagon'
		node#redundancy#target#style = 'filled'
		path#passed#color = 'lawngreen'
		path#passed#shape = 'tripleoctagon'
		path#passed#style = 'filled'
		path#failed#color = 'red'
		path#failed#shape = 'doubleoctagon'
		path#failed#style = 'filled'
		path#inconclusive#color = 'orange'
		path#inconclusive#shape = 'octagon'
		path#inconclusive#style = 'filled'
		path#aborted#color = 'red'
		path#aborted#shape = 'octagon'
		path#aborted#style = 'filled'
	] // end css
	trace [
		com = "[*]"
		variable = "[*]"
		path#condition = "leaf"
		// See full grammar of [Trace Specification] at the end of this generated file
	] // end trace
	vfs [
		file = "symbex_output.gv"
	] // end vfs
}

*/

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool CommonExecutionGraphSerializer::configureImpl(const WObject * wfParameterObject,
		EvaluationEnvironment & ENV, WrapData & aWrapData)
{
	// the Trace Point Filter configuration
	bool aConfigFlag = mTraceFilter.configure(ENV, wfParameterObject);

	mTraceFilter.setTracePointID(1);

	std::size_t error = 0;

	mContextNodeSeparator = "\\n";

	mInfoPattern = STANDARD_INFO_PATTERN;
	mInfoJustification = "";
	mInfoSeparator = "\\n";


	const WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));
	if( theFORMAT != WObject::_NULL_ )
	{
		aWrapData.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
			CONS_WID3("line", "wrap", "separator"), aWrapData.SEPARATOR);
		StringTools::replaceAll(aWrapData.SEPARATOR, "\\\\l", "\\l");

		error += configureFormatter(theFORMAT,
				mGlobalHeaderPattern, "header" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mGlobalEndPattern, "end" ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mContextNodePattern, "node" ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeLabelPattern,
				CONS_WID2("node", "label"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeCssAttributes,
				CONS_WID2("node", "css"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mContextEdgePattern, "edge" ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mContextNodeHeaderPattern,
				CONS_WID2("node", "header"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeDataPattern,
				CONS_WID2("node", "data"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeInfoPattern,
				CONS_WID2("node", "info"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeTraceRunPattern,
				OR_WID2(CONS_WID3("node", "trace", "run"),
				CONS_WID2("node", "fired")), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeTraceIOPattern,
				OR_WID2(CONS_WID3("node", "trace", "io"),
				CONS_WID2("node", "trace")), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeFlagsPattern,
				CONS_WID2("node", "flags"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mInfoPattern, "info" ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mPathConditionPattern,
				CONS_WID2("path", "condition"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mPathTimedConditionPattern,
				CONS_WID3("path", "timed", "condition"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mNodeConditionPattern,
				CONS_WID2("node", "condition"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mNodeTimedConditionPattern,
				CONS_WID3("node", "timed", "condition"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mAssignVariablePattern, "assign" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mNewfreshPattern, "newfresh" ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mAssignBufferPattern,
				CONS_WID2("assign", "buffer"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mInputPattern, "input" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mOutputPattern, "output" ) ? 0 : 1;


		error += configureFormatter(theFORMAT,
				mInputEnvPattern, CONS_WID2("input", "env"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mOutputEnvPattern, CONS_WID2("output", "env"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mInputRdvPattern , CONS_WID2("input", "rdv"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mOutputRdvPattern, CONS_WID2("output", "rdv"), true) ? 0 : 1;


		if( Query::hasWPropertyString(theFORMAT, "input") )
		{
			if( not Query::hasRegexWProperty(
					theFORMAT, CONS_WID2("input", "env")) )
			{
				mInputEnvPattern = mInputPattern;
			}
			if( not Query::hasRegexWProperty(
					theFORMAT, CONS_WID2("input", "rdv")) )
			{
				mInputRdvPattern = mInputPattern;
			}
		}

		if( Query::hasWPropertyString(theFORMAT, "output") )
		{
			if( not Query::hasRegexWProperty(
					theFORMAT, CONS_WID2("output", "env")) )
			{
				mOutputEnvPattern = mOutputPattern;
			}

			if( not Query::hasRegexWProperty(
					theFORMAT, CONS_WID2("output", "rdv")) )
			{
				mOutputRdvPattern = mOutputPattern;
			}
		}


		error += configureFormatter(theFORMAT, mLifelineStatePattern,
				CONS_WID2("lifeline", "state"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mStateKindPattern,
				CONS_WID2("state", "kind"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mMachinePattern, "machine" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mStatemachinePattern, "statemachine" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mStatePattern, "state" ) ? 0 : 1;


		error += configureFormatter(theFORMAT,
				mTransitionPattern, "transition") ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mRoutinePattern, "routine" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mVariablePattern, "variable" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mBufferPattern, "buffer" ) ? 0 : 1;
	}

	const WObject * theCSS = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("css", "CSS"));
	if( theCSS != WObject::_NULL_ )
	{
		mContextNodeCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID2("node", "color"), mContextNodeCssColor);
		mContextNodeCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID2("node", "shape"), mContextNodeCssShape);
		mContextNodeCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID2("node", "style"), mContextNodeCssStyle);


		mContextNodePassedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "passed", "color"), mContextNodePassedCssColor);
		mContextNodePassedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "passed", "shape"), mContextNodePassedCssShape);
		mContextNodePassedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "passed", "style"), mContextNodePassedCssStyle);

		mContextNodeFailedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "failed", "color"), mContextNodeFailedCssColor);
		mContextNodeFailedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "failed", "shape"), mContextNodeFailedCssShape);
		mContextNodeFailedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "failed", "style"), mContextNodeFailedCssStyle);

		mContextNodeInconclusiveCssColor = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("node", "inconclusive", "color"),
				mContextNodeInconclusiveCssColor);
		mContextNodeInconclusiveCssShape = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("node", "inconclusive", "shape"),
				mContextNodeInconclusiveCssShape);
		mContextNodeInconclusiveCssStyle = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("node", "inconclusive", "style"),
				mContextNodeInconclusiveCssStyle);

		mContextNodeAbortedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "aborted", "color"), mContextNodeAbortedCssColor);
		mContextNodeAbortedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "aborted", "shape"), mContextNodeAbortedCssShape);
		mContextNodeAbortedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "aborted", "style"), mContextNodeAbortedCssStyle);

		mContextNodeTimeoutCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "timeout", "color"), mContextNodeTimeoutCssColor);
		mContextNodeTimeoutCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "timeout", "shape"), mContextNodeTimeoutCssShape);
		mContextNodeTimeoutCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "timeout", "style"), mContextNodeTimeoutCssStyle);


		mContextNodeWarningCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "warning", "color"), mContextNodeWarningCssColor);
		mContextNodeWarningCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "warning", "shape"), mContextNodeWarningCssShape);
		mContextNodeWarningCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "warning", "style"), mContextNodeWarningCssStyle);

		mContextNodeErrorCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "error", "color"), mContextNodeErrorCssColor);
		mContextNodeErrorCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "error", "shape"), mContextNodeErrorCssShape);
		mContextNodeErrorCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "error", "style"), mContextNodeErrorCssStyle);

		mContextNodeAlertCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "alert", "color"), mContextNodeAlertCssColor);
		mContextNodeAlertCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "alert", "shape"), mContextNodeAlertCssShape);
		mContextNodeAlertCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "alert", "style"), mContextNodeAlertCssStyle);

		mContextNodeExitCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "exit", "color"), mContextNodeExitCssColor);
		mContextNodeExitCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "exit", "shape"), mContextNodeExitCssShape);
		mContextNodeExitCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("node", "exit", "style"), mContextNodeExitCssStyle);


		mContextNodeRedundancySourceCssColor = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "source", "color"),
				mContextNodeRedundancySourceCssColor);
		mContextNodeRedundancySourceCssShape = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "source", "shape"),
				mContextNodeRedundancySourceCssShape);
		mContextNodeRedundancySourceCssStyle = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "source", "style"),
				mContextNodeRedundancySourceCssStyle);

		mContextNodeRedundancyTargetCssColor = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "target", "color"),
				mContextNodeRedundancyTargetCssColor);
		mContextNodeRedundancyTargetCssShape = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "target", "shape"),
				mContextNodeRedundancyTargetCssShape);
		mContextNodeRedundancyTargetCssStyle = Query::getRegexWPropertyString(
				theCSS, CONS_WID4("node", "redundancy", "target", "style"),
				mContextNodeRedundancyTargetCssStyle);


		mContextPathPassedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "passed", "color"), mContextPathPassedCssColor);
		mContextPathPassedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "passed", "shape"), mContextPathPassedCssShape);
		mContextPathPassedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "passed", "style"), mContextPathPassedCssStyle);

		mContextPathFailedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "failed", "color"), mContextPathFailedCssColor);
		mContextPathFailedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "failed", "shape"), mContextPathFailedCssShape);
		mContextPathFailedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "failed", "style"), mContextPathFailedCssStyle);

		mContextPathInconclusiveCssColor = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("path", "inconclusive", "color"),
				mContextPathInconclusiveCssColor);
		mContextPathInconclusiveCssShape = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("path", "inconclusive", "shape"),
				mContextPathInconclusiveCssShape);
		mContextPathInconclusiveCssStyle = Query::getRegexWPropertyString(
				theCSS, CONS_WID3("path", "inconclusive", "style"),
				mContextPathInconclusiveCssStyle);

		mContextPathAbortedCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "aborted", "color"), mContextPathAbortedCssColor);
		mContextPathAbortedCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "aborted", "shape"), mContextPathAbortedCssShape);
		mContextPathAbortedCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "aborted", "style"), mContextPathAbortedCssStyle);

		mContextPathTimeoutCssColor = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "timeout", "color"), mContextPathTimeoutCssColor);
		mContextPathTimeoutCssShape = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "timeout", "shape"), mContextPathTimeoutCssShape);
		mContextPathTimeoutCssStyle = Query::getRegexWPropertyString(theCSS,
				CONS_WID3("path", "timeout", "style"), mContextPathTimeoutCssStyle);


//		mContextNodeSeparator = "\\n";
//
//		mInfoPattern = STANDARD_INFO_PATTERN;
//		mInfoJustification = "";
//		mInfoSeparator = "\\n";
	}

	mShowNodeHeaderFlag = (not mContextNodeHeaderPattern.empty());
	mShowNodeDataFlag   = (not mContextNodeDataPattern.empty());
	mShowNodeInfoFlag   = (not mContextNodeInfoPattern.empty());

	aConfigFlag =  (error == 0) && aConfigFlag;

	return( aConfigFlag );
}


bool CommonExecutionGraphSerializer::configureFormatter(const WObject * FORMAT,
		std::string & formatPattern, const std::string & id, bool isRegex)
{
	formatPattern = isRegex
			? Query::getRegexWPropertyString(FORMAT, id, formatPattern)
			: Query::getWPropertyString(FORMAT, id, formatPattern);

	StringTools::replaceAllEscapeSequences(formatPattern);

	try
	{
		boost::format formatter(formatPattern);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute(FORMAT, id, bfs.what());

		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FACTORY API used by PYTHON BINDINGS
////////////////////////////////////////////////////////////////////////////////

bool CommonExecutionGraphSerializer::configureDefaultImpl(
		bool showTransition, bool showCommunication, bool showAssign)
{
	if( showTransition )
	{
		mTraceFilter.addAnyTransitionFilter();
	}
	if( showCommunication )
	{
		mTraceFilter.addAnyComFilter();
	}
	if( showAssign )
	{
		mTraceFilter.addAnyAssignFilter();
	}

	mTraceFilter.setTracePointID(0);

	mContextNodePattern = "\nEC%1% [%2%%3%\n]";
	mContextNodeLabelPattern = "\n\tlabel=\"%2%%3%\"";
	mContextNodeDataPattern = "\n\n%3%%4%%5%%6%%2%%7%";

	mContextNodePassedCssColor = "black";

	mTransitionPattern = "%3%";
	mAssignVariablePattern = "%3% = %4%";

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		showTransition || showCommunication || showAssign)

	AVM_OS_TRACE << "CommonExecutionGraphSerializer->TraceFilter:> ";
	mTraceFilter.toStream(AVM_OS_TRACE);

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	return true;
}

} /* namespace sep */
