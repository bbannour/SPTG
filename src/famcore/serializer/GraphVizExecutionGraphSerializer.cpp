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

/**
 * GLOBAL HEADER / END
 * %1% --> graph name-id
 */
const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_GLOBAL_HEADER_PATTERN = "digraph %1% {";

const std::string & GraphVizExecutionGraphSerializer::
DEFAULT_GLOBAL_END_PATTERN = "\n}";


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool GraphVizExecutionGraphSerializer::configureImpl()
{
	mConfigFlag = Serializer::configureImpl();

	mConfigFlag = CommonExecutionGraphSerializer::configureImpl(
			getParameterWObject(), getENV(), mWrapData) && mConfigFlag;

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
//AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
//		showTransition || showCommunication || showAssign)
//
//	AVM_OS_TRACE << "GraphVizExecutionGraphSerializer->TraceFilter:> ";
//	mTraceFilter.toStream(AVM_OS_TRACE);
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

		return CommonExecutionGraphSerializer::configureDefaultImpl(
				showTransition, showCommunication, showAssign);
	}

	return false;
}


static const std::string ERROR_MESSAGE = R""""(
digraph fscn {

ERROR [
	label=" Unfound, in the current SymbexControllerUnitManager,
an existing GraphVizStatemachineSerializer
which configuration could be used
to configure the default GraphViz's serializer !
"
	shape=tripleoctagon
	color=red
	style=filled
]

}
)"""";


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

	out << ERROR_MESSAGE << std::endl;
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
			% "symbex_graph";
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
			% "symbex_graph";
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
 * %8% --> node#flags
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
	StringOutStream ecFlags( out );

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

	if( anEC.getFlags().hasReachedLimitOrExecutionTrace() )
	{
		/*
		 * EXECUTION CONTEXT FLAGS
		 * %1% --> node#id
		 * %2% --> flags
		 */
		boost::format formatterFlags(mContextNodeFlagsPattern);
		formatterFlags.exceptions( boost::io::no_error_bits );
		ecFlags << formatterFlags
				% anEC.getIdNumber()
				% anEC.getFlags().str();
	}

	/*
	 * EXECUTION CONTEXT NODE LABEL
	 * %1% --> node#id
	 * %2% --> node#header
	 * %3% --> node#data
	 * %4% --> node#info
	 * %5% --> node#trace#run
	 * %6% --> node#trace#io
	 * %7% --> node#flags
	 */
	boost::format formatterLabel(mContextNodeLabelPattern);
	formatterLabel.exceptions( boost::io::no_error_bits );

	ecLabel << formatterLabel
				% anEC.getIdNumber()
				% ecHeader.str()
				% ecData.str()
				% ecInfo.str()
				% ecFired.str()
				% ecTrace.str()
				% ecFlags.str();

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
			% ecTrace.str()
			% ecFlags.str();

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

//		std::string lifeline = aRID.hasLifeline() ?
//				aRID.getLifeline().getInstance()->getNameID() : "<no_lifeline>";

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
			anEC.getPrevious()->getExecutionData() : ExecutionData::nullref() );

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
			anEC.getPrevious()->getExecutionData() : ExecutionData::nullref() );

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
