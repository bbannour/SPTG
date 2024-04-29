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

#include "GraphVizExecutionGraphSerializer.h"

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
 * GLOBAL HEADER / END
 * %1% --> graph name-id
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_GLOBAL_HEADER_PATTERN = "digraph %1% {";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_GLOBAL_END_PATTERN = "\n}";

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
const std::string & GraphVizExecutionGraphSerializer::
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
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_LABEL_PATTERN = "\n\tlabel=\"%2%%4%\"";

/**
 * EXECUTION CONTEXT NODE CSS ATTRIBUTES
 * %1% --> node#id
 * %2% --> node#color
 * %3% --> node#shape
 * %4% --> node#style
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_CSS_ATTRIBUTES =
		"\n\tcolor=%2%\n\tshape=%3%\n\tstyle=%4%";

// CSS PROFILE: COLOR / SHAPE / STYLE

// NODE DEFAULT CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_CSS_COLOR = "lightblue";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_CSS_SHAPE = "box"; //"ellipse";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_CSS_STYLE = "rounded"; //"filled";

// NODE PASSED CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_COLOR = "yellow";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_PASSED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE FAILED CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_SHAPE = "doubleoctagon";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_FAILED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE INCONCLUSIVE CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_INCONCLUSIVE_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ABORTED CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_COLOR = "red";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_SHAPE = "octagon";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ABORTED_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE TIMEOUT CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_SHAPE = "octagon";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_TIMEOUT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE WARNING CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_WARNING_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ERROR CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_COLOR = "red";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ERROR_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE ALERT CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_COLOR = "red";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_ALERT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE EXIT CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_COLOR = "yellow";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_SHAPE = CONTEXT_NODE_CSS_SHAPE;

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_EXIT_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE REDUNDANCY_SOURCE CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_COLOR = "green";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_SHAPE = "cds";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_SOURCE_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;

// NODE REDUNDANCY_TARGET CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_COLOR = "greenyellow";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_SHAPE = "septagon";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_NODE_REDUNDANCY_TARGET_CSS_STYLE = CONTEXT_NODE_CSS_STYLE;


// PATH PASSED CSS
const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_PATH_PASSED_CSS_COLOR = "lawngreen";

const std::string & GraphVizExecutionGraphSerializer::
CONTEXT_PATH_PASSED_CSS_SHAPE = "tripleoctagon";

const std::string & GraphVizExecutionGraphSerializer::
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
const std::string & GraphVizExecutionGraphSerializer::
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
const std::string & GraphVizExecutionGraphSerializer::
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
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_DATA_PATTERN = "\nEC%1% -> ED%1%\nED%1% "
		"[\n\tlabel=\"%3%%4%%5%%6%%2%%7%\"\n\tshape=box\n]";

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution info
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_INFO_PATTERN = "\n%2%";
//		"\nEC%1% -> EI%1%\nEI%1% [\n\tlabel=\"%2%\""
//		"\n\tshape=octagon\n\tcolor=yellow\n\tstyle=filled\n]";

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution fired
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_FIRED_PATTERN = "%2%";

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution trace
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_TRACE_PATTERN = "%2%";

/**
 * INFO
 * %1% --> info id
 * %2% --> info data
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INFO_PATTERN = "%1%: %2%";

const std::string & GraphVizExecutionGraphSerializer::
STANDARD_INFO_PATTERN = "%2%";

/**
 * CONDITION
 *  %1% --> condition
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_PATH_CONDITION_PATTERN = "" /*"PC: %1%"*/;

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_PATH_TIMED_CONDITION_PATTERN = "" /*"PtC: %1%"*/;

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_NODE_CONDITION_PATTERN = "" /*"NC: %1%"*/;

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_NODE_TIMED_CONDITION_PATTERN = ""/*"NtC: %1%"*/;

/**
 * ASSIGN BUFFER
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> buffer identifier
 * %4% --> value
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_ASSIGN_BUFFER_PATTERN = "%2%:%3% = %4%";

/**
 * ASSIGN VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> (variable | buffer) identifier
 * %4% --> value
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_ASSIGN_VARIABLE_PATTERN = "%2%:%3% = %4%";

/**
 * NEWFRESH VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & GraphVizExecutionGraphSerializer::
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
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INPUT_PATTERN = "%2%->%3% ? %4%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_PATTERN = "%2%->%3% ! %4%";


const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INPUT_ENV_PATTERN = "env => %2%->%3% ? %4%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_ENV_PATTERN = "env <= %2%->%3% ! %4%";


const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INPUT_RDV_PATTERN = "\tinput#rdv  %2%->%3%%4%\n";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_RDV_PATTERN = "\toutput#rdv %2%->%3%%4%\n";


/**
 * LIFELINE STATE IDENTIFIER
 * %1% --> lifeline runtime pid
 * %2% --> lifeline identifier
 * %3% --> state runtime pid
 * %4% --> state identifier
 * %5% --> state kind
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_LIFELINE_STATE_PATTERN = "%2%:%4%";

/**
 * STATE KIND IDENTIFIER
 * %1% --> initial | final
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_STATE_KIND_PATTERN = "%1%";

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> machine identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_MACHINE_PATTERN = "%3%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_STATEMACHINE_PATTERN = "%3%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_STATE_PATTERN = "%3%";

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> transition identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_TRANSITION_PATTERN = "%2%->%3%";

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_ROUTINE_PATTERN = "%2%->%3%";

/**
 * VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_VARIABLE_PATTERN = "%1%->%3%";


/**
 * BUFFER
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> buffer identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_BUFFER_PATTERN = "%1%->%3%";





/*******************************************************************************
serializer += GraphVizExecutionGraphSerializer <name-id> "<description>" {
	// ...

@property:

@trace:

@format:

@vfs:
	file = "<save-file-path>"
}
*******************************************************************************/

/**
prototype processor::serializer#graph "serialize graph" as GraphVizExecutionGraphSerializer is
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

bool GraphVizExecutionGraphSerializer::configureImpl()
{
	mConfigFlag = Serializer::configureImpl();

	// the Trace Point Filter configuration
	mConfigFlag = mTraceFilter.configure(getENV(), getParameterWObject())
			&& mConfigFlag;

	mTraceFilter.setTracePointID(1);

	std::size_t error = 0;

	mContextNodeSeparator = "\\n";

	mInfoPattern = STANDARD_INFO_PATTERN;
	mInfoJustification = "";
	mInfoSeparator = "\\n";


	const WObject * theFORMAT = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("format", "FORMAT"));
	if( theFORMAT != WObject::_NULL_ )
	{
		mWrapData.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
			CONS_WID3("line", "wrap", "separator"), mWrapData.SEPARATOR);
		StringTools::replaceAll(mWrapData.SEPARATOR, "\\\\l", "\\l");

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
			getParameterWObject(), OR_WID2("css", "CSS"));
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

	mConfigFlag =  (error == 0) && mConfigFlag;

	if( mConfigFlag && mTraceFilter.hasNodeConditionTracePoint() )
	{
		getConfiguration().setNodeConditionComputationEnabled( true );
	}

	return( mConfigFlag );
}


bool GraphVizExecutionGraphSerializer::configureFormatter(const WObject * FORMAT,
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



/**
 * REPORT TRACE
 */
void GraphVizExecutionGraphSerializer::reportDefault(OutStream & out) const
{
	AVM_OS_VERBOSITY_MEDIUM( out )
			<< TAB << "GRAPHVIZ EXECUTION GRAPH SERIALIZER< "
			<< getParameterWObject()->getFullyQualifiedNameID()
			<< " > DONE !!!"  << EOL_FLUSH;
}


/**
 * FILTERING API
 */
bool GraphVizExecutionGraphSerializer::prefilter()
{
	return( true );
}

bool GraphVizExecutionGraphSerializer::postfilter()
{
	return( true );
}


/**
 * POST-PROCESSING API
 */
bool GraphVizExecutionGraphSerializer::postprocess()
{
	bool saveFlag = String::USE_BACKSLASH_QUOTE;
	String::USE_BACKSLASH_QUOTE = true;

	beginStream();
	while( hasStream() )
	{
		dotFormat(currentStream(), getConfiguration().getExecutionTrace());
	}

	// One graph per file for more readability
	if( getConfiguration().getExecutionTrace().populated() )
	{
		uint32_t offset = 0;

		for( const auto & rootEC : getConfiguration().getExecutionTrace() )
		{
			OutStream & currentSymbexGraphStream = newFileStream(offset++);

			ListOfExecutionContext graphEC( rootEC );

			dotFormat(currentSymbexGraphStream, graphEC);
		}
	}

	String::USE_BACKSLASH_QUOTE = saveFlag;

	closeStream();

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FACTORY API used by PYTHON BINDINGS
////////////////////////////////////////////////////////////////////////////////

bool GraphVizExecutionGraphSerializer::configureDefaultImpl(
		bool showTransition, bool showCommunication, bool showAssign)
{
	if( configureImpl() )
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

	AVM_OS_TRACE << "GraphVizExecutionGraphSerializer->TraceFilter:> ";
	mTraceFilter.toStream(AVM_OS_TRACE);

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )


		return true;
	}

	return false;
}

void GraphVizExecutionGraphSerializer::format(
		SymbexControllerUnitManager & aManager,
		OutStream & out, const ListOfExecutionContext & rootECs,
		bool showTransition, bool showCommunication, bool showAssign)
{
	AbstractProcessorUnit * existingSerializer =
			aManager.getControllerUnit(
					GraphVizExecutionGraphSerializer::AUTO_REGISTER_TOOL);

	if( existingSerializer != nullptr )
	{
		GraphVizExecutionGraphSerializer gvSerializer(
				aManager, existingSerializer->getParameterWObject());

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.dotFormat(out, rootECs);

			return;
		}
	}
	else
	{
		GraphVizExecutionGraphSerializer gvSerializer(aManager, WObject::_NULL_);

		if( gvSerializer.configureDefaultImpl(
				showTransition, showCommunication, showAssign) )
		{
			gvSerializer.dotFormat(out, rootECs);

			return;
		}
	}

	out << "digraph fscn {" << std::endl
		<< "ERROR [ " << std::endl
		<< "\tlabel=\""
		<< "Unfound,\n"
			"in the current SymbexControllerUnitManager,\\n"
			"an existing GraphVizExecutionGraphSerializer\\n"
			"which configuration could be used\n"
			"to configure the default GraphViz's serializer!\""
		<< std::endl
		<< "\tshape=tripleoctagon" << std::endl
		<< "\tcolor=red" << std::endl
		<< "\tstyle=filled"  << std::endl
		<< "]" << std::endl
		<< "}" << std::endl;
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void GraphVizExecutionGraphSerializer::dotFormat(
		OutStream & out, const ListOfExecutionContext & rootECs)
{
	out.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	doFormatHeader( out );

	mDotFormatNodeWaitingQueue.append( rootECs );

	const ExecutionContext * itEC = nullptr;
	while( mDotFormatNodeWaitingQueue.nonempty() )
	{
		mDotFormatNodeWaitingQueue.pop_first_to( itEC );

		dotFormatNode(out, (* itEC));
	}

	doFormatEnd( out );

	out.restoreSymbexValueCSS();
}

/**
 * GLOBAL HEADER
 * %1% --> graph name-id
 */
void GraphVizExecutionGraphSerializer::doFormatHeader(OutStream & out)
{
	boost::format formatter(mGlobalHeaderPattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << formatter
			% "fscn";
}

/**
 * GLOBAL END
 * %1% --> graph name#id
 */
void GraphVizExecutionGraphSerializer::doFormatEnd(OutStream & out)
{
	boost::format formatter(mGlobalEndPattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << formatter
			% "fscn";
}


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
void GraphVizExecutionGraphSerializer::dotFormatNode(
		OutStream & out, const ExecutionContext & anEC)
{
	StringOutStream ecLabel( out );
	StringOutStream ecCSS( out );

	StringOutStream ecHeader( out );
	StringOutStream ecData( out );
	StringOutStream ecInfo( out );
	StringOutStream ecFired( out );
	StringOutStream ecTrace( out );

	if( mShowNodeHeaderFlag )
	{
		dotFormatNodeHeader(ecHeader, anEC);
	}
	if( mShowNodeDataFlag )
	{
		dotFormatNodeData(ecData, anEC);
	}
	if( mShowNodeInfoFlag )
	{
		dotFormatNodeInfo(ecInfo, anEC);
	}
	if( mTraceFilter.hasRunnablePoint() )
	{
		dotFormatNodeRunnableTrace(ecFired, anEC);
	}
	if( mTraceFilter.hasIOTracePoint() )
	{
		dotFormatNodeIOTrace(ecFired, anEC);
	}

	/*
	 * EXECUTION CONTEXT NODE LABEL
	 * %1% --> node#id
	 * %2% --> node#header
	 * %3% --> node#data
	 * %4% --> node#info
	 * %5% --> node#trace#run
	 * %6% --> node#trace#io
	 */
	boost::format formatterLabel(mContextNodeLabelPattern);
	formatterLabel.exceptions( boost::io::no_error_bits );

	ecLabel << formatterLabel
				% anEC.getIdNumber()
				% ecHeader.str()
				% ecData.str()
				% ecInfo.str()
				% ecFired.str()
				% ecTrace.str();

	/*
	 * EXECUTION CONTEXT NODE CSS ATTRIBUTES
	 * %1% --> node#id
	 * %2% --> node#color
	 * %3% --> node#shape
	 * %4% --> node#style
	 */
	boost::format formatterCSS(mContextNodeCssAttributes);
	formatterCSS.exceptions( boost::io::no_error_bits );

	ecCSS << formatterCSS
			% anEC.getIdNumber()
			% dotNodeColor( anEC )
			% dotNodeShape( anEC )
			% dotNodeStyle( anEC );

	/*
	 * EXECUTION CONTEXT NODE
	 * %1% --> node#id
	 * %2% --> node#label
	 * %3% --> node#css
	 * %4% --> node#data
	 * %5% --> node#info
	 * %6% --> node#trace#run
	 * %7% --> node#trace#io
	 */
	boost::format formatter(mContextNodePattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << formatter
			% anEC.getIdNumber()
			% ecLabel.str()
			% ecCSS.str()
			% ecData.str()
			% ecInfo.str()
			% ecFired.str()
			% ecTrace.str();

	for( const auto & itEC : anEC.getChildContexts() )
	{
		dotFormatEdge(out, anEC, *itEC);

		mDotFormatNodeWaitingQueue.push_back( itEC );
	}
}


std::string GraphVizExecutionGraphSerializer::dotNodeColor(
		const ExecutionContext & anEC)
{
	const ExecutionContextFlags & flags = anEC.getFlags();

	if( flags.hasObjectiveAchieved() )
	{
		return( mContextPathPassedCssColor );
	}
	if( flags.hasObjectiveInconclusive() )
	{
		return( mContextPathInconclusiveCssColor );
	}
	if( flags.hasObjectiveFailed() )
	{
		return( mContextPathFailedCssColor );
	}
	if( flags.hasObjectiveAborted() )
	{
		return( mContextPathAbortedCssColor );
	}
	if( flags.hasObjectiveTimeout() )
	{
		return( mContextPathTimeoutCssColor );
	}

	if( flags.hasError() )
	{
		return( mContextNodeErrorCssColor );
	}

	if( flags.isExecutionStatementExitTrace() )
	{
		return( mContextNodeExitCssColor );
	}

	if( flags.hasAlert() )
	{
		return( mContextNodeAlertCssColor );
	}

	if( flags.hasWarning() )
	{
		return( mContextNodeWarningCssColor );
	}

	if( flags.hasRedundancy() )
	{
		return( mContextNodeRedundancySourceCssColor );
	}

	if( flags.hasRedundancyTarget() )
	{
		return( mContextNodeRedundancyTargetCssColor );
	}

	if( flags.hasCoverageElement() /*&& anEC.hasInfo()*/ )
	{
		return( mContextNodePassedCssColor );
	}

	return( mContextNodeCssColor );
}

std::string GraphVizExecutionGraphSerializer::dotNodeShape(
		const ExecutionContext & anEC)
{
	const ExecutionContextFlags & flags = anEC.getFlags();

	if( flags.hasObjectiveAchieved() )
	{
		return( mContextPathPassedCssShape );
	}
	if( flags.hasObjectiveInconclusive() )
	{
		return( mContextPathInconclusiveCssShape );
	}
	if( flags.hasObjectiveFailed() )
	{
		return( mContextPathFailedCssShape );
	}
	if( flags.hasObjectiveAborted() )
	{
		return( mContextPathAbortedCssShape );
	}
	if( flags.hasObjectiveTimeout() )
	{
		return( mContextPathTimeoutCssShape );
	}

	if( flags.isExecutionStatementExitTrace() )
	{
		return( mContextNodeExitCssShape );
	}

	if( flags.hasRedundancy() )
	{
		return( mContextNodeRedundancySourceCssShape );
	}

	if( flags.hasRedundancyTarget() )
	{
		return( mContextNodeRedundancyTargetCssShape );
	}

	if( flags.hasCoverageElement() /*&& anEC.hasInfo()*/ )
	{
		return( mContextNodePassedCssShape );
	}

	return( mContextNodeCssShape );
}

std::string GraphVizExecutionGraphSerializer::dotNodeStyle(
		const ExecutionContext & anEC)
{
	const ExecutionContextFlags & flags = anEC.getFlags();

	if( flags.hasObjectiveAchieved() )
	{
		return( mContextPathPassedCssStyle );
	}
	if( flags.hasObjectiveInconclusive() )
	{
		return( mContextPathInconclusiveCssStyle );
	}
	if( flags.hasObjectiveFailed() )
	{
		return( mContextPathFailedCssStyle );
	}
	if( flags.hasObjectiveAborted() )
	{
		return( mContextPathAbortedCssStyle );
	}
	if( flags.hasObjectiveTimeout() )
	{
		return( mContextPathTimeoutCssStyle );
	}

	if( flags.isExecutionStatementExitTrace() )
	{
		return( mContextNodeExitCssStyle );
	}

	if( flags.hasRedundancy() )
	{
		return( mContextNodeRedundancySourceCssStyle );
	}

	if( flags.hasRedundancyTarget() )
	{
		return( mContextNodeRedundancyTargetCssStyle );
	}

	if( flags.hasCoverageElement() /*&& anEC.hasInfo()*/ )
	{
		return( mContextNodePassedCssStyle );
	}

	return( mContextNodeCssStyle );
}


/**
 * EXECUTION CONTEXT EDGE
 * %1% --> node#source#id
 * %2% --> node#target#id
 * %3% --> node#target#data
 * %4% --> node#target#info
 * %5% --> node#target#fired
 * %6% --> node#target#trace
 */
void GraphVizExecutionGraphSerializer::dotFormatInfo(
		OutStream & out, const GenericInfoData & anInfo)
{
	std::string strInfo = anInfo.strData();
	if( not strInfo.empty() )
	{
		boost::format formatter(mInfoPattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% anInfo.strUID()
				% strInfo;

		out << mInfoJustification;
	}
}



void GraphVizExecutionGraphSerializer::dotFormatEdge(OutStream & out,
		const ExecutionContext & srcEC, const ExecutionContext & tgtEC)
{
	StringOutStream ecData( out );
	StringOutStream ecInfo( out );
	StringOutStream ecFired( out );
	StringOutStream ecTrace( out );

	if( mShowNodeDataFlag )
	{
		dotFormatNodeData(ecData, tgtEC);
	}
	if( mShowNodeInfoFlag )
	{
		dotFormatNodeInfo(ecInfo, tgtEC);
	}
	if( mTraceFilter.hasRunnablePoint() )
	{
		dotFormatNodeRunnableTrace(ecFired, tgtEC);
	}
	if( mTraceFilter.hasIOTracePoint() )
	{
		dotFormatNodeIOTrace(ecFired, tgtEC);
	}

	boost::format formatter(mContextEdgePattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << formatter
			% srcEC.getIdNumber()
			% tgtEC.getIdNumber()
			% ecData.str()
			% ecInfo.str()
			% ecFired.str()
			% ecTrace.str();
}


/**
 * EXECUTION CONTEXT HEADER
 * %1% --> ec#id
 * %2% --> ec#eval
 * %3% --> ec#hight
 * %4% --> ec#width
 * %5% --> ec#weight
 * %6% --> statemachine configuration i.e. lifelines state identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeHeader(
		OutStream & out, const ExecutionContext & anEC)
{
	boost::format formatter(mContextNodeHeaderPattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << formatter
			% anEC.getIdNumber()
			% anEC.getEvalNumber()
			% anEC.getHeight()
			% anEC.getWidth()
			% anEC.getWeight()
			% anEC.getExecutionData().strStateConf(mLifelineStatePattern);

	if( anEC.getFlags().hasReachedLimitOrExecutionTrace() )
	{
		out << "\\n" << anEC.getFlags().str();
	}
}

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
void GraphVizExecutionGraphSerializer::dotFormatNodeData(
		OutStream & out, const ExecutionContext & anEC)
{
	StringOutStream edAssign( out );
	StringOutStream edPC( out );
	StringOutStream edPtC( out );
	StringOutStream edFC( out );
	StringOutStream edFtC( out );
	StringOutStream edBuffer( out );

	bool hasData = false;

	const ExecutionData & anED = anEC.getExecutionData();

	if( mTraceFilter.hasPathConditionPoint()
		&& (not anED.getPathCondition().isEqualTrue()) )
	{
		dotFormatCondition(edPC, mPathConditionPattern,
				anED.getPathCondition() );

		hasData = true;
	}
	else if( mTraceFilter.hasPathConditionLeafNodePoint()
			&& anEC.isLeafNode()
			&& (not anED.getPathCondition().isEqualTrue()) )
	{
		dotFormatCondition(edPC, mPathConditionPattern,
				anED.getPathCondition() );

		hasData = true;
	}

	if( mTraceFilter.hasPathTimedConditionPoint()
		&& (not anED.getPathTimedCondition().isEqualTrue()) )
	{
		dotFormatCondition(edPtC, mPathTimedConditionPattern,
				anED.getPathTimedCondition() );

		hasData = true;
	}
	else if( mTraceFilter.hasPathTimedConditionLeafNodePoint()
			&& anEC.isLeafNode()
			&& (not anED.getPathTimedCondition().isEqualTrue()) )
	{
		dotFormatCondition(edPtC, mPathTimedConditionPattern,
				anED.getPathTimedCondition() );

		hasData = true;
	}

	if( mTraceFilter.hasNodeConditionPoint()
		&& (not anED.getNodeCondition().isEqualTrue()) )
	{
		dotFormatCondition(edFC, mNodeConditionPattern,
				anED.getNodeCondition() );

		hasData = true;
	}
	if( mTraceFilter.hasNodeTimedConditionPoint()
		&& (not anED.getNodeTimedCondition().isEqualTrue()) )
	{
		dotFormatCondition(edFtC, mNodeTimedConditionPattern,
				anED.getNodeTimedCondition() );

		hasData = true;
	}

	if( mTraceFilter.hasAssignPoint() )
	{
		dotFormatAssignVariable(edAssign, anEC, anEC.isnotRoot());

		hasData = hasData || (not edAssign.str().empty());
	}

	if( mTraceFilter.hasComBufferPoint() )
	{
		dotFormatAssignBuffer(edBuffer, anEC, anEC.isnotRoot());

		hasData = hasData || (not edBuffer.str().empty());
	}


	if( hasData )
	{
		boost::format formatter(mContextNodeDataPattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% anEC.getIdNumber()
				% edAssign.str()
				% edPC.str()
				% edPtC.str()
				% edFC.str()
				% edFtC.str()
				% edBuffer.str();
	}
}

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution info
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeInfo(
		OutStream & out, const ExecutionContext & anEC)
{
	if( anEC.hasInfo() )
	{
		StringOutStream ecInfo( out );

		BFList::const_ref_iterator<
				GenericInfoData > itInfo = anEC.getInfos().begin();
		BFList::const_ref_iterator<
				GenericInfoData > endInfo = anEC.getInfos().end();
		dotFormatInfo(ecInfo, itInfo);
		for( ++itInfo ; itInfo != endInfo ; ++itInfo )
		{
			ecInfo << mInfoSeparator;
			dotFormatInfo(ecInfo, itInfo);
		}

		std::string strInfo = ecInfo.str();
		if( not strInfo.empty() )
		{
			boost::format formatter(mContextNodeInfoPattern);
			formatter.exceptions( boost::io::no_error_bits );

			out << formatter
					% anEC.getIdNumber()
					% strInfo;
		}
	}
}


/**
 * INFO
 * %1% --> info id
 * %2% --> info data
 */
/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution fired
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeRunnableTrace(
		OutStream & out, const ExecutionContext & anEC)
{
	if( anEC.hasRunnableElementTrace() )
	{
		StringOutStream ecFired( out );
		dotFormatRunnableTrace(ecFired, anEC.getRunnableElementTrace());

		std::string strFired = ecFired.str();

		if( not strFired.empty() )
		{
			boost::format formatter(mContextNodeTraceRunPattern);
			formatter.exceptions( boost::io::no_error_bits );

			out << formatter
					% anEC.getIdNumber()
					% strFired;
		}
	}
}

/**
 * FIRED
 * running machine
 * fired transition
 * invoked routine
 */
void GraphVizExecutionGraphSerializer::dotFormatRunnableTrace(
		OutStream & out, const BF & aFired)
{
	if( aFired.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aFired.to< ExecutionConfiguration >();

		if( aConf.isTransition() )
		{
			dotFormatTransition(out, aConf.getRuntimeID(), aConf.toTransition());
		}
		else if( aConf.isOperator() &&
				aConf.getOperator().isOpCode( AVM_OPCODE_RUN ) )
		{
			const Specifier & specifier = aConf.getRuntimeID().getSpecifier();
			if( specifier.isFamilyComponentState() )
			{
				dotFormatMachine(out, aConf.getRuntimeID(), mStatePattern);
			}
			else if( specifier.isFamilyComponentStatemachine()
					&& specifier.isMocStateTransitionStructure() )
			{
				dotFormatMachine(out, aConf.getRuntimeID(), mStatemachinePattern);
			}
			else
			{
				dotFormatMachine(out, aConf.getRuntimeID(), mMachinePattern);
			}
		}
	}
	else if( aFired.is< AvmCode >() )
	{
		const AvmCode & aCode = aFired.to< AvmCode >();

		for( const auto & itOperand : aCode.getOperands() )
		{
			dotFormatRunnableTrace(out, itOperand);
		}
	}
}

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> machine identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatMachine(
		OutStream & out, const RuntimeID & aRID, const std::string & pattern)
{
	if( mTraceFilter.pass(aRID) )
	{
		boost::format formatter(pattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% aRID.strPid()
				% (aRID.hasParent() ?
						aRID.getParent().getInstance()->getNameID() : "root")
				% aRID.getInstance()->getNameID();

		out << mWrapData.SEPARATOR;
	}
}

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> transition identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatTransition(OutStream & out,
		const RuntimeID & aRID, const AvmTransition & aTransition)
{
	if( mTraceFilter.hasTransitionPoint()
		&& 	mTraceFilter.pass(aTransition) )
	{
		boost::format formatter(mTransitionPattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% aRID.getLifeline().getInstance()->getNameID()
				% aRID.getInstance()->getNameID()
				% aTransition.getNameID();

		out << mWrapData.SEPARATOR;
	}
}

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatRoutine(OutStream & out,
		const RuntimeID & aRID, const AvmProgram & aRoutine)
{
	if( mTraceFilter.hasRoutinePoint() )
	{
		boost::format formatter(mRoutinePattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% aRID.strPid()
				% aRID.getInstance()->getNameID()
				% aRoutine.getNameID();

		out << mWrapData.SEPARATOR;
	}
}


/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution trace
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeIOTrace(
		OutStream & out, const ExecutionContext & anEC)
{
	StringOutStream ecTrace( out );
	dotFormatIOTrace(ecTrace, anEC, anEC.getIOElementTrace());

	std::string strTrace = ecTrace.str();

	if( not strTrace.empty() )
	{
		boost::format formatter(mContextNodeTraceIOPattern);
		formatter.exceptions( boost::io::no_error_bits );

		out << formatter
				% anEC.getIdNumber()
				% strTrace;
	}
}

/**
 * TRACE
 * input  ( port | signal | message ) [ values ]
 * output ( port | signal | message ) [ values ]
 * newfresh variable <- value
 */
void GraphVizExecutionGraphSerializer::dotFormatIOTrace(
		OutStream & out, const ExecutionContext & anEC, const BF & aTrace)
{
	if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aConf.isAvmCode()
			&& filterExecutionConfiguration(mTraceFilter, anEC, aConf) )
		{
			const AvmCode & aCode = aConf.toAvmCode();

			switch( aCode.getOptimizedOpCode() )
			{
				case AVM_OPCODE_INPUT_ENV:
				{
					dotFormatInputOutput(out, mInputEnvPattern, aConf);

					break;
				}
				case AVM_OPCODE_INPUT_RDV:
				{
					dotFormatInputOutput(out, mInputRdvPattern, aConf);

					break;
				}
				case AVM_OPCODE_INPUT:
				{
					dotFormatInputOutput(out, mInputPattern, aConf);

					break;
				}

				case AVM_OPCODE_OUTPUT_ENV:
				{
					dotFormatInputOutput(out, mOutputEnvPattern, aConf);

					break;
				}
				case AVM_OPCODE_OUTPUT_RDV:
				{
					dotFormatInputOutput(out, mOutputRdvPattern, aConf);

					break;
				}
				case AVM_OPCODE_OUTPUT:
				{
					dotFormatInputOutput(out, mOutputPattern, aConf);

					break;
				}

				case AVM_OPCODE_ASSIGN_NEWFRESH:
				{
					dotFormatNewfresh(out, aConf);

					break;
				}

				default:
				{
					break;
				}
			}
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = aTrace.to< AvmCode >();

		for( const auto & itOperand : aCode.getOperands() )
		{
			dotFormatIOTrace(out, anEC, itOperand);
		}
	}
}


/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> port | signal | message  identifier
 * %4% --> value
 * %5% --> machine sender   identifier name
 * %6% --> machine receiver identifier name
 * %7% --> message $timestamp
 */
void GraphVizExecutionGraphSerializer::dotFormatInputOutput(OutStream & out,
		const std::string & pattern, const ExecutionConfiguration & anExecConf)
{
	const AvmCode & aCode = anExecConf.toAvmCode();

	const InstanceOfPort & aPort = aCode.first().to< InstanceOfPort >();

	OSS oss( AVM_STR_INDENT , out );

	if( aCode.hasManyOperands() )
	{
		AvmCode::const_iterator itOperand = aCode.begin();
		AvmCode::const_iterator endOperand = aCode.end();
		if( (++itOperand) != endOperand )
		{
			oss << oss.VALUE_PARAMS_CSS.BEGIN;

			aPort.getParameterType(0).formatStream(oss, (*itOperand));

			std::size_t offset = 1;
			for( ++itOperand ; itOperand != endOperand ; ++itOperand , ++offset )
			{
				oss << oss.VALUE_PARAMS_CSS.SEPARATOR;

				aPort.getParameterType(offset).formatStream(oss, (*itOperand));
			}

			oss << oss.VALUE_PARAMS_CSS.END;
		}
	}

	const RuntimeID & aRID = anExecConf.getRuntimeID();
	RuntimeID ridContainer = aRID.getCommunicator( aPort );

	std::string strSender    = "<<sender#unknown>>";
	std::string strReciever  = "<<receiver#unknown>>";
	std::string strTimestamp = "$timestamp";

	const Message & message = anExecConf.getIOMessage();

	if( message.valid() )
	{
		if( message.hasSenderRID() )
		{
			strSender = message.getLifelineSenderRID().getInstance()->getNameID();
		}
		if( message.hasReceiverRID() )
		{
			strReciever = message.getLifelineReceiverRID().getInstance()->getNameID();
		}
		else if ( aCode.isOpCode( AVM_OPCODE_INPUT ) )
		{
			strReciever = aRID.getLifeline().getInstance()->getNameID();
		}
	}
	else if ( aCode.isOpCode( AVM_OPCODE_OUTPUT ) )
	{
		strSender = aRID.getLifeline().getInstance()->getNameID();
	}
	else if ( aCode.isOpCode( AVM_OPCODE_INPUT ) )
	{
		strReciever = aRID.getLifeline().getInstance()->getNameID();
	}

	if( anExecConf.hasTimestamp() )
	{
		strTimestamp = anExecConf.getTimestamp().str();
	}

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << mWrapData << formatter
			% ridContainer.strPid()
			% ridContainer.getInstance()->getNameID()
			% aCode.first().to< InstanceOfPort >().getNameID()
			% oss.str()
			% strSender
			% strReciever
			% strTimestamp;

	out << END_WRAP << mWrapData.SEPARATOR;
}


/**
 * ASSIGN
 * aConf.ment: var = value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssignBuffer(
		OutStream & out, const ExecutionContext & anEC, bool isnotRoot)
{
	const ExecutionData & anED = anEC.getExecutionData();
	const ExecutionData & prevED = ( isnotRoot ?
			anEC.getPrevious()->getExecutionData() : ExecutionData::_NULL_ );

	avm_offset_t endOffset = 0;
	avm_offset_t offset = 0;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = nullptr;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasBuffer() )
		{
			endOffset = pRF->refExecutable().getBuffer().size();
			for( offset = 0 ; offset < endOffset ; ++offset)
			{
				const InstanceOfBuffer & aBuffer =
						pRF->refExecutable().getBuffer().get(offset).asBuffer();

				const BaseBufferForm & aBufferValue = pRF->getBuffer(& aBuffer);

				if( mDataSelectionModifiedFlags && isnotRoot )
				{
					if( aBufferValue.equals( prevED.getRuntime(
							pRF->getRID() ).getBuffer(& aBuffer) ) )
					{
						continue;
					}
				}

				if( mTraceFilter.pass(pRF->getRID(), aBuffer) )
				{
					dotFormatAssignBuffer(out,
							pRF->getRID(), aBuffer, aBufferValue);
				}
			}
		}
	}
}

/**
 * ASSIGN BUFFER
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssignBuffer(OutStream & out,
		const RuntimeID & aRID, const InstanceOfBuffer & aBuffer,
		const BaseBufferForm & aBufferValue)
{
	boost::format formatter(mAssignBufferPattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << mWrapData << formatter
			% aRID.strPid()
			% aRID.getInstance()->getNameID()
			% aBuffer.getNameID()
//			% aBuffer.strValue( aBufferValue );
			% aBufferValue.strValue();

	out << END_WRAP << mWrapData.SEPARATOR;
}



/**
 * NEWFRESH VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void GraphVizExecutionGraphSerializer::dotFormatNewfresh(
		OutStream & out, const ExecutionConfiguration & anExecConf)
{
	const AvmCode & aCode = anExecConf.toAvmCode();

	const InstanceOfData & aVariable = aCode.first().to< InstanceOfData >();

	boost::format formatter(mNewfreshPattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID ridContainer =
			anExecConf.getRuntimeID().getAncestorContaining( aVariable );

	out << mWrapData << formatter
			% ridContainer.strPid()
			% ridContainer.getInstance()->getNameID()
			% aVariable.getNameID()
			% aVariable.strValue( aCode.second() );

	out << END_WRAP << mWrapData.SEPARATOR;
}


/**
 * CONDITION
 * [ Timed ] [ Path | Fired ] Condition
 */
void GraphVizExecutionGraphSerializer::dotFormatCondition(OutStream & out,
		const std::string & formatPattern, const BF & aCondition)
{
	boost::format formatter(formatPattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << mWrapData << formatter
			% aCondition.str();

	out << END_WRAP << mWrapData.SEPARATOR;
}

/**
 * ASSIGN
 * Assignment: var = value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssignVariable(
		OutStream & out, const ExecutionContext & anEC, bool isnotRoot)
{
	const ExecutionData & anED = anEC.getExecutionData();
	const ExecutionData & prevED = ( isnotRoot ?
			anEC.getPrevious()->getExecutionData() : ExecutionData::_NULL_ );

	avm_offset_t endOffset = 0;
	avm_offset_t offset = 0;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = nullptr;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasData() )
		{
			endOffset = pRF->refExecutable().getBasicVariables().size();
			for( offset = 0 ; offset < endOffset ; ++offset)
			{
				const InstanceOfData & aVariable =
						pRF->refExecutable().getBasicVariables().refAt(offset);
				
				const BF & aValue = pRF->getData(& aVariable);

				if( mDataSelectionModifiedFlags && isnotRoot )
				{
//					if( not pRF->isAssigned(aVariable) )
//					if( not anED.isAssigned(pRF->getRID(), aVariable.getOffset()) )
					if( aValue == prevED.getRuntime(
							pRF->getRID()).getData(& aVariable) )
					{
						continue;
					}
				}

				if( mTraceFilter.pass(pRF->getRID(), aVariable) )
				{
					dotFormatAssignVariable(out, pRF->getRID(), aVariable, aValue);
				}
			}
		}
	}
}

/**
 * ASSIGN VARIABLE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssignVariable(OutStream & out,
		const RuntimeID & aRID, const InstanceOfData & aVar, const BF & aValue)
{
	boost::format formatter(mAssignVariablePattern);
	formatter.exceptions( boost::io::no_error_bits );

	out << mWrapData << formatter
			% aRID.strPid()
			% aRID.getInstance()->getNameID()
			% aVar.getNameID()
			% aVar.strValue( aValue );

	out << END_WRAP << mWrapData.SEPARATOR;
}


} /* namespace sep */
