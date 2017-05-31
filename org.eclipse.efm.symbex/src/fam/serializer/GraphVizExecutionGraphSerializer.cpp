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

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>

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
 * %6% --> node#fired
 * %7% --> node#trace
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_PATTERN = "\nEC%1% [%2%%3%\n]%4%";

/**
 * EXECUTION CONTEXT NODE LABEL
 * %1% --> node#id
 * %2% --> node#header
 * %3% --> node#data
 * %4% --> node#info
 * %5% --> node#fired
 * %6% --> node#trace
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_LABEL_PATTERN = "\n\tlabel=\"%2%%4%\"";

/**
 * EXECUTION CONTEXT NODE CSS
 * %1% --> node#id
 * %2% --> node#color
 * %3% --> node#shape
 * %4% --> node#style
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_CSS_PATTERN =
		"\n\tcolor=%2%\n\tshape=%3%\n\tstyle=%4%";

// CSS PROFILE: COLOR / SHAPE
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_COLOR = "lightblue";

const std::string & GraphVizExecutionGraphSerializer::
WARNING_CONTEXT_NODE_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
ERROR_CONTEXT_NODE_COLOR = "red";

const std::string & GraphVizExecutionGraphSerializer::
ALERT_CONTEXT_NODE_COLOR = "red";


const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_ACHIEVED_CONTEXT_NODE_COLOR = "lawngreen";

const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_ACHIEVED_CONTEXT_NODE_SHAPE = "tripleoctagon";


const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_FAILED_CONTEXT_NODE_COLOR = "orange";

const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_FAILED_CONTEXT_NODE_SHAPE = "doubleoctagon";


const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_ABORTED_CONTEXT_NODE_COLOR = "red";

const std::string & GraphVizExecutionGraphSerializer::
OBJECTIVE_ABORTED_CONTEXT_NODE_SHAPE = "octagon";


const std::string & GraphVizExecutionGraphSerializer::
COVERAGE_ELEMENT_CONTEXT_NODE_COLOR = "yellow";


const std::string & GraphVizExecutionGraphSerializer::
REDUNDANCY_CONTEXT_NODE_COLOR = "green";

const std::string & GraphVizExecutionGraphSerializer::
REDUNDANCY_CONTEXT_NODE_SHAPE = "cds";

const std::string & GraphVizExecutionGraphSerializer::
REDUNDANCY_TARGET_CONTEXT_NODE_COLOR = "greenyellow";

const std::string & GraphVizExecutionGraphSerializer::
REDUNDANCY_TARGET_CONTEXT_NODE_SHAPE = "septagon";

// CSS PROFILE: SHAPE
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_SHAPE = "ellipse";

const std::string & GraphVizExecutionGraphSerializer::
STATEMENT_EXIT_CONTEXT_NODE_SHAPE = "tripleoctagon";

// CSS PROFILE: STYLE
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_STYLE = "filled";


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
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_CONTEXT_NODE_DATA_PATTERN = "\nEC%1% -> ED%1%\nED%1% "
		"[\n\tlabel=\"%3%%4%%5%%6%%2%\"\n\tshape=box\n]";

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
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_ASSIGN_PATTERN = "%1%:%2% = %3%";

/**
 * NEWFRESH
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_NEWFRESH_PATTERN = "newfresh %1%->%2%( %3% )";

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
DEFAULT_INPUT_PATTERN = "%1%->%3% ? %4%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_PATTERN = "%1%->%3% ! %4%";


const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INPUT_ENV_PATTERN = "env => %1%->%3% ? %4%";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_ENV_PATTERN = "env <= %1%->%3% ! %4%";


const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_INPUT_RDV_PATTERN = "\tinput#rdv  %2%->%3%%4%\n";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_OUTPUT_RDV_PATTERN = "\toutput#rdv %2%->%3%%4%\n";


/**
 * LIFELINE STATE IDENTIFIER
 * %1% --> lifeline runtime pid
 * %2% --> lifeline identifier
 * %3% --> state runtime pid
 * %3% --> state identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_LIFELINE_STATE_PATTERN = "%2%:%4%";

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> machine identifier
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_MACHINE_PATTERN = "%3%";

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
	// %6% --> node#fired
	// %7% --> node#trace
	@node = "\nEC%1% [%2%%3%\n]%5%%4%";

	// %1% --> node#id
	// %2% --> node#header
	// %3% --> node#data
	// %4% --> node#info
	// %5% --> node#fired
	// %6% --> node#trace
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
	@node#data = "\nEC%1% -> ED%1%\nED%1% [\n\tlabel=\"%3%%4%%5%%6%%2%\"\n\tshape=box\n]";

	// %1% --> node#id
	// %2% --> execution info
	@node#info = "\nEC%1% -> EI%1%\nEI%1% [\n\tlabel=\"%2%\"\n\tshape=box\n\tcolor=yellow\n\tstyle=filled\n]";

	// %1% --> node#id
	// %2% --> execution fired
	@node#fired = "%2%";

	// %1% --> node#id
	// %2% --> execution trace
	@node#trace = "%2%";


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

	avm_size_t error = 0;

	// Standard profile
	mContextNodeColor   = DEFAULT_CONTEXT_NODE_COLOR;
	mContextNodeShape   = DEFAULT_CONTEXT_NODE_SHAPE;
	mContextNodeStyle   = DEFAULT_CONTEXT_NODE_STYLE;

	mContextNodeSeparator = "\\n";

	mInfoPattern = STANDARD_INFO_PATTERN;
	mInfoJustification = "";
	mInfoSeparator = "\\n";


	WObject * theFORMAT = Query::getRegexWSequence(
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
		error += configureFormatter(theFORMAT, mContextNodeCssPattern,
				CONS_WID2("node", "css"), true ) ? 0 : 1;

		error += configureFormatter(theFORMAT,
				mContextEdgePattern, "edge" ) ? 0 : 1;

		error += configureFormatter(theFORMAT, mContextNodeHeaderPattern,
				CONS_WID2("node", "header"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeDataPattern,
				CONS_WID2("node", "data"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeInfoPattern,
				CONS_WID2("node", "info"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeFiredPattern,
				CONS_WID2("node", "fired"), true ) ? 0 : 1;
		error += configureFormatter(theFORMAT, mContextNodeTracePattern,
				CONS_WID2("node", "trace"), true ) ? 0 : 1;

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
				mAssignPattern, "assign" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mNewfreshPattern, "newfresh" ) ? 0 : 1;

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

		error += configureFormatter(theFORMAT,
				mMachinePattern, "machine" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mTransitionPattern, "transition") ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mRoutinePattern, "routine" ) ? 0 : 1;
		error += configureFormatter(theFORMAT,
				mVariablePattern, "variable" ) ? 0 : 1;
	}
//	else // Standard profile
//	{
//		mContextNodeColor   = DEFAULT_CONTEXT_NODE_COLOR;
//		mContextNodeShape   = DEFAULT_CONTEXT_NODE_SHAPE;
//		mContextNodeStyle   = DEFAULT_CONTEXT_NODE_STYLE;
//
//		mContextNodeSeparator = "\\n";
//
//		mInfoPattern = STANDARD_INFO_PATTERN;
//		mInfoJustification = "";
//		mInfoSeparator = "\\n";
//	}

	mShowNodeHeaderFlag = (not mContextNodeHeaderPattern.empty());
	mShowNodeDataFlag   = (not mContextNodeDataPattern.empty());
	mShowNodeInfoFlag   = (not mContextNodeInfoPattern.empty());

	mConfigFlag =  (error == 0) && mConfigFlag;

	return( mConfigFlag );
}


bool GraphVizExecutionGraphSerializer::configureFormatter(WObject * FORMAT,
		std::string & formatPattern, const std::string & id, bool isRegex)
{
	formatPattern = isRegex
			? Query::getRegexWPropertyString(FORMAT, id, formatPattern)
			: Query::getWPropertyString(FORMAT, id, formatPattern);

	StringTools::replaceAll(formatPattern, "\\t" , "\t");
	StringTools::replaceAll(formatPattern, "\\n" , "\n");
	StringTools::replaceAll(formatPattern, "\\\"", "\"");

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
void GraphVizExecutionGraphSerializer::reportDefault(OutStream & os) const
{
	AVM_OS_VERBOSITY_MEDIUM( os )
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
	const ExecutionContext & anEC = *( getConfiguration().getFirstTrace() );

	bool saveFlag = String::USE_BACKSLASH_QUOTE;
	String::USE_BACKSLASH_QUOTE = true;

	beginStream();
	while( hasStream() )
	{
		dotFormat(currentStream(), anEC);
	}

	String::USE_BACKSLASH_QUOTE = saveFlag;

	closeStream();

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// DEFAULT FORMAT API
////////////////////////////////////////////////////////////////////////////

void GraphVizExecutionGraphSerializer::format(
		SymbexControllerUnitManager & aManager,
		OutStream & out, const ExecutionContext & rootEC)
{
	AbstractProcessorUnit * existingSerializer =
			aManager.getControllerUnit(
					GraphVizExecutionGraphSerializer::AUTO_REGISTER_TOOL);

	if( existingSerializer != NULL )
	{
		GraphVizExecutionGraphSerializer gvSerializer(
				aManager, existingSerializer->getParameterWObject());

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.dotFormat(out, rootEC);

			return;
		}
	}
	else
	{
		GraphVizExecutionGraphSerializer gvSerializer(aManager, WObject::_NULL_);

		if( gvSerializer.configureImpl() )
		{
			gvSerializer.dotFormat(out, rootEC);

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
		OutStream & os, const ExecutionContext & rootEC)
{
	os.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	doFormatHeader( os );

	mDotFormatNodeWaitingQueue.push_back( & rootEC );

	const ExecutionContext * itEC = NULL;
	while( mDotFormatNodeWaitingQueue.nonempty() )
	{
		mDotFormatNodeWaitingQueue.pop_first_to( itEC );

		dotFormatNode(os, (* itEC));
	}

	doFormatEnd( os );

	os.restoreSymbexValueCSS();
}

/**
 * GLOBAL HEADER
 * %1% --> graph name-id
 */
void GraphVizExecutionGraphSerializer::doFormatHeader(OutStream & os)
{
	boost::format formatter(mGlobalHeaderPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% "fscn";
}

/**
 * GLOBAL END
 * %1% --> graph name#id
 */
void GraphVizExecutionGraphSerializer::doFormatEnd(OutStream & os)
{
	boost::format formatter(mGlobalEndPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% "fscn";
}


/**
 * EXECUTION CONTEXT NODE
 * %1% --> node#id
 * %2% --> node#label
 * %3% --> node#css
 * %4% --> node#data
 * %5% --> node#info
 * %6% --> node#fired
 * %7% --> node#trace
 */
void GraphVizExecutionGraphSerializer::dotFormatNode(
		OutStream & os, const ExecutionContext & anEC)
{
	StringOutStream ecLabel;
	StringOutStream ecCSS;

	StringOutStream ecHeader;
	StringOutStream ecData;
	StringOutStream ecInfo;
	StringOutStream ecFired;
	StringOutStream ecTrace;

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
	 * %5% --> node#fired
	 * %6% --> node#trace
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
	 * EXECUTION CONTEXT NODE CSS
	 * %1% --> node#id
	 * %2% --> node#color
	 * %3% --> node#shape
	 * %4% --> node#style
	 */
	boost::format formatterCSS(mContextNodeCssPattern);
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
	 * %6% --> node#fired
	 * %7% --> node#trace
	 */
	boost::format formatter(mContextNodePattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% anEC.getIdNumber()
			% ecLabel.str()
			% ecCSS.str()
			% ecData.str()
			% ecInfo.str()
			% ecFired.str()
			% ecTrace.str();

	ExecutionContext::child_iterator itEC = anEC.begin();
	ExecutionContext::child_iterator endEC = anEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		dotFormatEdge(os, anEC, *(*itEC));

		mDotFormatNodeWaitingQueue.push_back( *itEC );
	}
}


std::string GraphVizExecutionGraphSerializer::dotNodeColor(
		const ExecutionContext & anEC)
{
	const ExecutionContextFlags & flags = anEC.getFlags();

	if( flags.hasObjectiveAchieved() )
	{
		return( OBJECTIVE_ACHIEVED_CONTEXT_NODE_COLOR );
	}
	if( flags.hasObjectiveFailed() )
	{
		return( OBJECTIVE_FAILED_CONTEXT_NODE_COLOR );
	}
	if( flags.hasObjectiveAborted() )
	{
		return( OBJECTIVE_ABORTED_CONTEXT_NODE_COLOR );
	}

	if( flags.hasError() )
	{
		return( ERROR_CONTEXT_NODE_COLOR );
	}

	if( flags.hasAlert() )
	{
		return( ALERT_CONTEXT_NODE_COLOR );
	}

	if( flags.hasWarning() )
	{
		return( WARNING_CONTEXT_NODE_COLOR );
	}

	if( flags.hasRedundancy() )
	{
		return( REDUNDANCY_CONTEXT_NODE_COLOR );
	}

	if( flags.hasRedundancyTarget() )
	{
		return( REDUNDANCY_TARGET_CONTEXT_NODE_COLOR );
	}

	if( flags.hasCoverageElement() /*&& anEC.hasInfo()*/ )
	{
		return( COVERAGE_ELEMENT_CONTEXT_NODE_COLOR );
	}

	return( mContextNodeColor );
}

std::string GraphVizExecutionGraphSerializer::dotNodeShape(
		const ExecutionContext & anEC)
{
	const ExecutionContextFlags & flags = anEC.getFlags();

	if( flags.hasObjectiveAchieved() )
	{
		return( OBJECTIVE_ACHIEVED_CONTEXT_NODE_SHAPE );
	}
	if( flags.hasObjectiveFailed() )
	{
		return( OBJECTIVE_FAILED_CONTEXT_NODE_SHAPE );
	}
	if( flags.hasObjectiveAborted() )
	{
		return( OBJECTIVE_ABORTED_CONTEXT_NODE_SHAPE );
	}

	if( flags.isExecutionStatementExitTrace() )
	{
		return( STATEMENT_EXIT_CONTEXT_NODE_SHAPE );
	}

	if( flags.hasRedundancy() )
	{
		return( REDUNDANCY_CONTEXT_NODE_SHAPE );
	}

	if( flags.hasRedundancyTarget() )
	{
		return( REDUNDANCY_TARGET_CONTEXT_NODE_SHAPE );
	}

	return( mContextNodeShape );
}

std::string GraphVizExecutionGraphSerializer::dotNodeStyle(
		const ExecutionContext & anEC)
{
	return( mContextNodeStyle );
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
		OutStream & os, GenericInfoData * anInfo)
{
	std::string strInfo = anInfo->strData();
	if( not strInfo.empty() )
	{
		boost::format formatter(mInfoPattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
				% anInfo->strUID()
				% strInfo
				<< mInfoJustification;
	}
}



void GraphVizExecutionGraphSerializer::dotFormatEdge(OutStream & os,
		const ExecutionContext & srcEC, const ExecutionContext & tgtEC)
{
	StringOutStream ecData;
	StringOutStream ecInfo;
	StringOutStream ecFired;
	StringOutStream ecTrace;

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

	os << formatter
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
		OutStream & os, const ExecutionContext & anEC)
{
	boost::format formatter(mContextNodeHeaderPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% anEC.getIdNumber()
			% anEC.getEvalNumber()
			% anEC.getHeight()
			% anEC.getWidth()
			% anEC.getWeight()
			% anEC.refExecutionData().strStateConf(mLifelineStatePattern);

	if( anEC.getFlags().hasReachedLimitOrExecutionTrace() )
	{
		os << "\\n" << anEC.getFlags().str();
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
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeData(
		OutStream & os, const ExecutionContext & anEC)
{
	StringOutStream edAssign;
	StringOutStream edPC;
	StringOutStream edPtC;
	StringOutStream edFC;
	StringOutStream edFtC;

	bool hasData = false;

	const ExecutionData & anED = anEC.refExecutionData();

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
		dotFormatAssign(edAssign, anED, anEC.isnotRoot());

		hasData = hasData || (not edAssign.str().empty());
	}


	if( hasData )
	{
		boost::format formatter(mContextNodeDataPattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
				% anEC.getIdNumber()
				% edAssign.str()
				% edPC.str()
				% edPtC.str()
				% edFC.str()
				% edFtC.str();
	}
}

/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution info
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeInfo(
		OutStream & os, const ExecutionContext & anEC)
{
	if( anEC.hasInfo() )
	{
		StringOutStream ecInfo;

		BFList::const_raw_iterator<
				GenericInfoData > itInfo = anEC.getInfos().begin();
		BFList::const_raw_iterator<
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

			os << formatter
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
		OutStream & os, const ExecutionContext & anEC)
{
	if( anEC.hasRunnableElementTrace() )
	{
		StringOutStream ecFired;
		dotFormatRunnableTrace(ecFired, anEC.getRunnableElementTrace());

		std::string strFired = ecFired.str();

		if( not strFired.empty() )
		{
			boost::format formatter(mContextNodeFiredPattern);
			formatter.exceptions( boost::io::no_error_bits );

			os << formatter
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
		OutStream & os, const BF & aFired)
{
	if( aFired.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * aConf =
				aFired.to_ptr< ExecutionConfiguration >();

		if( aConf->isTransition() )
		{
			dotFormatTransition(os,
					aConf->getRuntimeID(), aConf->getTransition());
		}
		else if( aConf->isOperator() &&
				aConf->getOperator()->isOpCode( AVM_OPCODE_RUN ) )
		{
			dotFormatMachine(os, aConf->getRuntimeID());
		}
	}
	else if( aFired.is< AvmCode >() )
	{
		AvmCode * aCode = aFired.to_ptr< AvmCode >();

		AvmCode::const_iterator it = aCode->begin();
		AvmCode::const_iterator endCode = aCode->end();
		for( ; it != endCode ; ++it )
		{
			dotFormatRunnableTrace(os, (*it));
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
		OutStream & os, const RuntimeID & aRID)
{
	if( mTraceFilter.pass(aRID) )
	{
		boost::format formatter(mMachinePattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
				% aRID.strPid()
				% aRID.getInstance()->getNameID()
				% aRID.getInstance()->getNameID()
				<< mWrapData.SEPARATOR;
	}
}

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> transition identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatTransition(OutStream & os,
		const RuntimeID & aRID, AvmTransition * aTransition)
{
	if( mTraceFilter.hasTransitionPoint() )
	{
		boost::format formatter(mTransitionPattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
				% aRID.strPid()
				% aRID.getInstance()->getNameID()
				% aTransition->getNameID()
				<< mWrapData.SEPARATOR;
	}
}

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
void GraphVizExecutionGraphSerializer::dotFormatRoutine(OutStream & os,
		const RuntimeID & aRID, AvmProgram * aRoutine)
{
	if( mTraceFilter.hasRoutinePoint() )
	{
		boost::format formatter(mRoutinePattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
				% aRID.strPid()
				% aRID.getInstance()->getNameID()
				% aRoutine->getNameID()
				<< mWrapData.SEPARATOR;
	}
}


/**
 * EXECUTION CONTEXT INFO
 * %1% --> node#id
 * %2% --> execution trace
 */
void GraphVizExecutionGraphSerializer::dotFormatNodeIOTrace(
		OutStream & os, const ExecutionContext & anEC)
{
	StringOutStream ecTrace;
	dotFormatIOTrace(ecTrace, anEC.getIOElementTrace());

	std::string strTrace = ecTrace.str();

	if( not strTrace.empty() )
	{
		boost::format formatter(mContextNodeTracePattern);
		formatter.exceptions( boost::io::no_error_bits );

		os << formatter
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
		OutStream & os, const BF & aTrace)
{
	if( aTrace.is< ExecutionConfiguration >() )
	{
		ExecutionConfiguration * aConf =
				aTrace.to_ptr< ExecutionConfiguration >();

		if( aConf->isAvmCode() )
		{
			AvmCode * aCode = aConf->getAvmCode();

			switch( aCode->getOptimizedOpCode() )
			{
				case AVM_OPCODE_INPUT_ENV:
				{
					if( mTraceFilter.hasInputEnvPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mInputEnvPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}
				case AVM_OPCODE_INPUT_RDV:
				{
					if( mTraceFilter.hasInputRdvPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mInputRdvPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}
				case AVM_OPCODE_INPUT:
				{
					if( mTraceFilter.hasInputPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mInputPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}

				case AVM_OPCODE_OUTPUT_ENV:
				{
					if( mTraceFilter.hasOutputEnvPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mOutputEnvPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}
				case AVM_OPCODE_OUTPUT_RDV:
				{
					if( mTraceFilter.hasOutputRdvPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mOutputRdvPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}
				case AVM_OPCODE_OUTPUT:
				{
					if( mTraceFilter.hasOutputPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatInputOutput(os, mOutputPattern,
								aConf->getRuntimeID(), aCode);
					}
					break;
				}

				case AVM_OPCODE_ASSIGN_NEWFRESH:
				{
					if( mTraceFilter.hasNewfreshPoint()
						&& mTraceFilter.pass(aCode) )
					{
						dotFormatNewfresh(os, aConf->getRuntimeID(), aCode);
					}
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
		AvmCode * aCode = aTrace.to_ptr< AvmCode >();

		AvmCode::const_iterator it = aCode->begin();
		AvmCode::const_iterator endCode = aCode->end();
		for( ; it != endCode ; ++it )
		{
			dotFormatIOTrace(os, (*it));
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
 */
void GraphVizExecutionGraphSerializer::dotFormatInputOutput(
		OutStream & os, const std::string & pattern,
		const RuntimeID & aRID, AvmCode * aCode)
{
	InstanceOfPort * aPort = aCode->first().to_ptr< InstanceOfPort >();

	OSS oss( AVM_STR_INDENT );

	if( aCode->populated() )
	{
		AvmCode::const_iterator it = aCode->begin();
		AvmCode::const_iterator endCode = aCode->end();
		if( (++it) != endCode )
		{
			oss << os.VALUE_PARAMS_CSS.BEGIN;

			aPort->getParameterType(0)->formatStream(oss, (*it));

			avm_size_t offset = 1;
			for( ++it ; it != endCode ; ++it , ++offset )
			{
				oss << os.VALUE_PARAMS_CSS.SEPARATOR;

				aPort->getParameterType(offset)->formatStream(oss, (*it));
			}

			oss << os.VALUE_PARAMS_CSS.END;
		}
	}

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID ridContainer = aRID.getCommunicator( aPort );

	os << mWrapData << formatter
			% ridContainer.strPid()
			% ridContainer.getInstance()->getNameID()
			% aCode->first().to_ptr< InstanceOfPort >()->getNameID()
			% oss.str();

	os << END_WRAP << mWrapData.SEPARATOR;
}


/**
 * NEWFRESH
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void GraphVizExecutionGraphSerializer::dotFormatNewfresh(OutStream & os,
		const RuntimeID & aRID, AvmCode * aCode)
{
	InstanceOfData * aVar = aCode->first().to_ptr< InstanceOfData >();

	boost::format formatter(mNewfreshPattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID ridContainer = aRID.getAncestorContaining(aVar);

	os << mWrapData << formatter
			% ridContainer.strPid()
			% ridContainer.getInstance()->getNameID()
			% aVar->getNameID()
			% aVar->strValue( aCode->second() );

	os << END_WRAP << mWrapData.SEPARATOR;
}


/**
 * CONDITION
 * [ Timed ] [ Path | Fired ] Condition
 */
void GraphVizExecutionGraphSerializer::dotFormatCondition(OutStream & os,
		const std::string & formatPattern, const BF & aCondition)
{
	boost::format formatter(formatPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter % aCondition.str();

	os << END_WRAP << mWrapData.SEPARATOR;
}

/**
 * ASSIGN
 * Assignment: var = value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssign(
		OutStream & os, const ExecutionData & anED, bool isnotRoot)
{
	TableOfInstanceOfData::const_raw_iterator itVariable;
	TableOfInstanceOfData::const_raw_iterator endVariable;

	TableOfRuntimeT::const_iterator itRF = anED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = anED.getTableOfRuntime().end();
	RuntimeForm * pRF = NULL;
	for( ++itRF; (itRF != endRF) ; ++itRF )
	{
		pRF = (*itRF);

		if( pRF->hasData() )
		{
			itVariable = pRF->getExecutable()->getAllData().begin();
			endVariable = pRF->getExecutable()->getAllData().end();
			for( ; itVariable != endVariable ; ++itVariable )
			{
				if( mDataSelectionModifiedFlags && isnotRoot )
				{
					if( not anED.isAssigned(
							pRF->getRID(), itVariable->getOffset()) )
					{
						continue;
					}
				}

				if( mTraceFilter.pass(pRF->getRID(),
						static_cast< InstanceOfData * >(itVariable)) )
				{
					dotFormatAssign(os, pRF->getRID(), itVariable,
							pRF->getDataTable()->get(itVariable));
				}
			}
		}
	}
}

/**
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void GraphVizExecutionGraphSerializer::dotFormatAssign(OutStream & os,
		const RuntimeID & aRID, InstanceOfData * aVar, const BF & aValue)
{
	boost::format formatter(mAssignPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter
			% aRID.strPid()
			% aRID.getInstance()->getNameID()
			% aVar->getNameID()
			% aVar->strValue( aValue );

	os << END_WRAP << mWrapData.SEPARATOR;
}


} /* namespace sep */
