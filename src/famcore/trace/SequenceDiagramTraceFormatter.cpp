/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SequenceDiagramTraceFormatter.h"

#include "SequenceDiagramTraceBuilder.h"
#include "AvmTraceGenerator.h"

#include "TraceManager.h"

#include <common/SerializerFeature.h>


#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/RuntimeQuery.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <boost/format.hpp>


namespace sep
{

unsigned int SequenceDiagramTraceFormatter::mIndexOfMessageInMap = 1;


/**
 * GLOBAL HEADER / END
 * %1% --> graph name-id
 */

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_GLOBAL_HEADER_PATTERN =
		"@startuml\n\n"
		"skinparam note{\n"
			"\tBackgroundColor White\n"
			"\tBorderColor White\n"
		"}\n\nskinparam BackgroundColor transparent\n\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_GLOBAL_END_PATTERN = "\n@enduml";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_CONTEXT_ACTION_PATTERN = "\naction";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_EXECUTION_CONTEXT_PATTERN = "ec_%1%";//< %1% > %6%

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_BOX_HEADER_PATTERN = "box \"%1%\" #transparent\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_BOX_END_PATTERN = "end box\n\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_PARTICIPANT_PATTERN = "participant %1%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_CONTEXT_NODE_SEPARATION_PATTERN = "EC#%1%<Ev:%2%>";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_PATH_HEADER_PATTERN = "== TRACE PATH %1% %2% ==\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_PATH_END_PATTERN = "\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_LIFELINE_HEADER_PATTERN = "group %3%\n";

//const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_LIFELINE_HEADER_PATTERN = "'LIFELINE %3% {\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_LIFELINE_END_PATTERN = "end\n\n";

//const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_LIFELINE_END_PATTERN = "'} // end lifeline %3%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_LIFELINE_ID_PATTERN = "%3%";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_INIT_HEADER_PATTERN = "\t// Initialization parameter values:\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_INIT_END_PATTERN = "\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_STEP_HEADER_PATTERN = "==%2%==\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_STEP_BEGIN_PATTERN = "group %2%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_STEP_END_PATTERN = "end\n\n";


const std::string & SequenceDiagramTraceFormatter::
DEFAULT_PATH_CONDITION_PATTERN = "note over %3%, %4% #pink : PC : %1%";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_PATH_TIMED_CONDITION_PATTERN = "note over %3%, %4% #9ACD32 : PtC : %1%";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_NODE_CONDITION_PATTERN = "note over of %2% #pink : NC : %1%";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_NODE_TIMED_CONDITION_PATTERN = "note over of %2% #9ACD32 : NtC : %1%";


/**
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_ASSIGN_PATTERN = "hnote over of %2% #yellow : %3% = %4%\n";
DEFAULT_ASSIGN_PATTERN = "note over %2% #yellow %3%%4%\nend note\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_TIME_PATTERN = "note right of timestamp : time elapsed %5%\n";

//const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_TIME_PATTERN = "note right of %2% : $time %4%\n";

/**
 * NEWFRESH
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_NEWFRESH_PATTERN = "note right of %2% : newfresh %2%->%3%( %4% )\n";

/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> ( port | signal ) identifier
 * %4% --> value
 * %5% --> machine sender   identifier name
 * %6% --> machine receiver identifier name
 * %7% --> index of message
 * %8% --> color of message
 * %9% --> timestamp of emission or reception
 */

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_INPUT_PATTERN = "%6% [%8%]-> %6% : <font color = %8%> msg#%7% ? %3% %4% \nactivate %6% \ndeactivate %6%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_OUTPUT_PATTERN = "%5% [%8%]-> %6% : <font color = %8%> msg#%7% ! %3% %4% \nactivate %6% \ndeactivate %6%\n";

//const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_INPUT_PATTERN = "%6% -> %6% : msg? %3% %4% \nactivate %6% \ndeactivate %6%\n";
//
//const std::string & SequenceDiagramTraceFormatter::
//DEFAULT_OUTPUT_PATTERN = "%5% -> %6% : msg! %3% %4% \nactivate %6% \ndeactivate %6%\n";


const std::string & SequenceDiagramTraceFormatter::
DEFAULT_INPUT_ENV_PATTERN = "-[#000000]> %6% : %3% %4%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_OUTPUT_ENV_PATTERN = "<[#000000]- %5% : %3% %4%\n";


const std::string & SequenceDiagramTraceFormatter::
DEFAULT_INPUT_RDV_PATTERN = "%6% [%8%]-> %6% : <font color = %8%> msg#%7% ? %3% %4%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_OUTPUT_RDV_PATTERN = "%5% [%8%]-> %6% : <font color = %8%> msg#%7% ! %3% %4%\n";

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine lifeline container identifier
 * %3% --> machine container identifier
 * %4% --> machine identifier
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_MACHINE_PATTERN = "hnote over of %2% #cyan : run %4%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_STATE_MACHINE_PATTERN = "hnote over of %2% #teal : %4%\n";

const std::string & SequenceDiagramTraceFormatter::
DEFAULT_STATE_PATTERN = "hnote over of %2% #gray : %4%\n";

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> lifeline identifier
 * %3% --> machine container identifier
 * %4% --> transition identifier
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_TRANSITION_PATTERN = "hnote over of %2% #orange : fired %2%->%4%\n";

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_ROUTINE_PATTERN = "%2%->%3%";


/**
 * META TRACE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> operand
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_META_TRACE_PATTERN = "%4%";

/**
 * META DEBUG
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> operand
 */
const std::string & SequenceDiagramTraceFormatter::
DEFAULT_META_DEBUG_PATTERN = "%4%";



// Color for messages

const std::string & SequenceDiagramTraceFormatter::
RED_COLOR = "#e6194b";

const std::string & SequenceDiagramTraceFormatter::
GREEN_COLOR = "#3cb44b";

const std::string & SequenceDiagramTraceFormatter::
BLUE_COLOR = "#4363d8";

const std::string & SequenceDiagramTraceFormatter::
ORANGE_COLOR = "#f58231";

const std::string & SequenceDiagramTraceFormatter::
PURPLE_COLOR = "#911eb4";

const std::string & SequenceDiagramTraceFormatter::
TEAL_COLOR = "#469990";

const std::string & SequenceDiagramTraceFormatter::
MAROON_COLOR = "#800000";

const std::string & SequenceDiagramTraceFormatter::
OLIVE_COLOR = "#808000";


/**
 * CONSTRUCTOR
 * Default
 */
SequenceDiagramTraceFormatter::SequenceDiagramTraceFormatter(AvmTraceGenerator & aTraceGenerator)
: AbstractTraceFormatter( aTraceGenerator ),
mFileHeaderPattern( DEFAULT_GLOBAL_HEADER_PATTERN ),
mFileBeginPattern( "" ),
mFileEndPattern( DEFAULT_GLOBAL_END_PATTERN ),

mBoxHeaderPattern( DEFAULT_BOX_HEADER_PATTERN ),

mBoxEndPattern( DEFAULT_BOX_END_PATTERN ),

mParticipantPattern( DEFAULT_PARTICIPANT_PATTERN ),

mExecutionContextUfidPattern( DEFAULT_EXECUTION_CONTEXT_PATTERN ),

mPathHeaderPattern( DEFAULT_PATH_HEADER_PATTERN ),
mPathBeginPattern( "" ),
mPathEndPattern( DEFAULT_PATH_END_PATTERN ),

mLifelineHeaderPattern( DEFAULT_LIFELINE_HEADER_PATTERN ),
mLifelineBeginPattern( "" ),
mLifelineEndPattern( DEFAULT_LIFELINE_END_PATTERN ),

mLifelineIdPattern( DEFAULT_LIFELINE_ID_PATTERN ),

mInitializationHeaderPattern( DEFAULT_INIT_HEADER_PATTERN ),
mInitializationBeginPattern( "" ),
mInitializationEndPattern( DEFAULT_INIT_END_PATTERN ),

mStepHeaderPattern( DEFAULT_STEP_HEADER_PATTERN ),
mStepBeginPattern ( DEFAULT_STEP_BEGIN_PATTERN  ),
mStepEndPattern   ( DEFAULT_STEP_END_PATTERN  ),

mCommentPattern  ( "== %1% ==\n" ),
mSeparatorPattern( "%1%"   ),
mNewlinePattern  ( "\n%1%" ),

mPathConditionPattern( DEFAULT_PATH_CONDITION_PATTERN ),
mPathTimedConditionPattern( DEFAULT_PATH_TIMED_CONDITION_PATTERN ),

mNodeConditionPattern( DEFAULT_NODE_CONDITION_PATTERN ),
mNodeTimedConditionPattern( DEFAULT_NODE_TIMED_CONDITION_PATTERN ),

mTimePattern( DEFAULT_TIME_PATTERN ),

mAssignPattern( DEFAULT_ASSIGN_PATTERN ),

mNewfreshPattern( DEFAULT_NEWFRESH_PATTERN ),

mInputPattern ( DEFAULT_INPUT_PATTERN  ),
mOutputPattern( DEFAULT_OUTPUT_PATTERN ),

mInputEnvPattern ( DEFAULT_INPUT_ENV_PATTERN  ),
mOutputEnvPattern( DEFAULT_OUTPUT_ENV_PATTERN ),

mInputRdvPattern ( DEFAULT_INPUT_RDV_PATTERN  ),
mOutputRdvPattern( DEFAULT_OUTPUT_RDV_PATTERN ),

mLifelineStatePattern( "%2%:%4%"  ),
mStateKindPattern( "%1%" ),

mMachinePattern     ( DEFAULT_MACHINE_PATTERN ),
mStatemachinePattern( DEFAULT_STATE_MACHINE_PATTERN ),
mStatePattern       ( DEFAULT_STATE_PATTERN ),

mTransitionPattern  ( DEFAULT_TRANSITION_PATTERN ),
mRoutinePattern     ( "\teval %1%->%2%\n" ),

mRunnablePattern   ( "\trun %1%->%2%\n" ),

mExecutionInformationPattern ( "\tinfo %1%"),

mMetaTracePattern( DEFAULT_META_TRACE_PATTERN ),
mMetaDebugPattern( DEFAULT_META_DEBUG_PATTERN ),

mWrapDataSeparator( "\\n" ),


////////////////////////////////////////////////////////////////////////////
// Computing Variables
ossValue( ),
mTraceSequence( nullptr ),
mMapOfLifelineAndId( ),
mMapOfColors( { {0, RED_COLOR}, {1, GREEN_COLOR}, {2, BLUE_COLOR},
	{3, ORANGE_COLOR}, {4, PURPLE_COLOR}, {5, TEAL_COLOR},
	{6, MAROON_COLOR}, {7, OLIVE_COLOR} } ),
mListOfParticipants( ),

mMapMessageReceiver( static_cast< SequenceDiagramTraceBuilder & >(
		aTraceGenerator.getTraceBuilder()).getMapMessageReceiver() )
{
	//!! NOTHING
}

/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 ...
 section FORMAT
  @line#wrap#width = 80;
  @line#wrap#separator = "\n\t";

  @header = "TRACE LIST\n";
  @end    = "\n";

  // %1% --> ->EC#id
  // %2% --> ec#eval
  // %3% --> ec#hight
  // %4% --> ec#width
  // %5% --> ec#weight
  // %6% --> statemachine configuration i.e. control node
  @context#qnid = "ctx< %1% > %6%";
  @context#ufid = "ctx< %1% > %6%"; // @Deprecated

  // %1% --> trace number
  // %2% --> execution context leaf identifier
  @header = "TRACE NUMBER %1%\n";
  @end    = "\n";

  @init#begin = "\t// Initialization parameter values:\n";
  @init#end    = "\n";

  // %1% --> string message
  // %2% --> execution context identifier
  @comment   = "//%1%";
  @separator = "%1%"  ;
  @newline   = "\n%1%";

  // %1% --> step identifier
  // %2% --> execution context identifier
  @step#begin = "#step#begin %1%\n";
  @step#end   = "#step#end %1%\n";

  // %1% --> condition
  // %2% --> execution context identifier
  @path#condition = "PC: %1%";
  @path#timed#condition = "PtC: %1%";
  @node#condition = "NC: %1%";
  @node#timed#condition = "NtC: %1%";

  // %1% --> machine runtime pid
  // %2% --> machine container identifier
  // %3% --> port | signal | variable | machine | transition | routine
  // %4% --> value

  @time   = "\t%4%\n";

  @assign = "\t%2%:%3% = %4%\n";

  @newfresh = "\tnewfresh %2%->%3%( %4% )\n";

  @input  = "\tinput  %2%->%3%%4%\n";
  @output = "\toutput %2%->%3%%4%\n";

  @input#env  = "\tINPUT  %2%->%3%%4%\n";
  @output#env = "\tOUTPUT %2%->%3%%4%\n";

 endsection FORMAT
 ...
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool SequenceDiagramTraceFormatter::configure(const WObject * FORMAT,
		std::string & formatPattern, const std::string & id, bool isRegex)
{
	formatPattern =  isRegex
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

bool SequenceDiagramTraceFormatter::configureImpl(const WObject * wfParameterObject)
{
	// default parameter
	// %1% --> trace number
	// %2% --> execution context leaf identifier
	// @header = "TRACE NUMBER %1%\n";
	// @end    = "\n";

	// %1% --> machine runtime pid
	// %2% --> machine container identifier
	// %3% --> port | signal | variable | machine | transition | routine
	// %4% --> value

	// @time   = "\t%4%\n";
	//
	// @assign = "\t%2%:%3% = %4%\n";
	//
	// @newfresh = "\tnewfresh %2%->%3%( %4% )\n";
	//
	// @input  = "\tinput  %2%->%3%%4%\n";
	// @output = "\toutput %2%->%3%%4%\n";

	const WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));

	if( theFORMAT != WObject::_NULL_ )
	{
		std::size_t error = 0;

		mWrapDataSeparator = mWrapData.SEPARATOR =
				Query::getRegexWPropertyString(theFORMAT,
					CONS_WID3("line", "wrap", "separator"), mWrapData.SEPARATOR);

		mWrapData.LINE_WIDTH = Query::getRegexWPropertySizeT(theFORMAT,
				CONS_WID3("line", "wrap", "width"), mWrapData.LINE_WIDTH);

		error += configure(theFORMAT, mExecutionContextUfidPattern,
				OR_WID2(CONS_WID3("execution", "context", "(qn|uf)?id"),
						CONS_WID2("context", "(qn|uf)?id")), true) ? 0 : 1;

		error += configure(theFORMAT, mFileHeaderPattern,
				CONS_WID2("file", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mFileBeginPattern,
				CONS_WID2("file", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mFileEndPattern,
				CONS_WID2("file", "end"), true   ) ? 0 : 1;

		error += configure(theFORMAT, mBoxHeaderPattern,
				CONS_WID2("box", "header"), true ) ? 0 : 1;

		error += configure(theFORMAT, mBoxEndPattern,
				CONS_WID2("end", "header"), true ) ? 0 : 1;

		error += configure(theFORMAT, mParticipantPattern,
				"participant", true ) ? 0 : 1;


		error += configure(theFORMAT, mPathHeaderPattern,
				CONS_WID2("testcase", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mPathBeginPattern,
				CONS_WID2("testcase", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mPathEndPattern,
				CONS_WID2("testcase", "end"), true   ) ? 0 : 1;


		error += configure(theFORMAT, mLifelineHeaderPattern,
				CONS_WID2("lifeline", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mLifelineBeginPattern,
				CONS_WID2("lifeline", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mLifelineEndPattern,
				CONS_WID2("lifeline", "end"), true   ) ? 0 : 1;

		error += configure(theFORMAT, mLifelineIdPattern,
				CONS_WID2("lifeline", "id"), true   ) ? 0 : 1;


		error += configure(theFORMAT, mInitializationHeaderPattern,
				CONS_WID2("init", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mInitializationBeginPattern,
				CONS_WID2("init", "begin"), true) ? 0 : 1;

		error += configure(theFORMAT, mInitializationEndPattern,
				CONS_WID2("init", "end"), true  ) ? 0 : 1;


		error += configure(theFORMAT, mStepHeaderPattern,
				CONS_WID2("step", "header"), true) ? 0 : 1;

		error += configure(theFORMAT,mStepBeginPattern,
				CONS_WID2("step", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mStepEndPattern,
				CONS_WID2("step", "end"), true   ) ? 0 : 1;


		error += configure(theFORMAT, mCommentPattern  , "comment"  ) ? 0 : 1;

		error += configure(theFORMAT, mSeparatorPattern, "separator") ? 0 : 1;

		error += configure(theFORMAT, mNewlinePattern  , "newline"  ) ? 0 : 1;


		error += configure(theFORMAT, mPathConditionPattern,
				CONS_WID2("path", "condition"), true ) ? 0 : 1;

		error += configure(theFORMAT,mPathTimedConditionPattern,
				CONS_WID3("path", "timed", "condition"), true ) ? 0 : 1;

		error += configure(theFORMAT, mNodeConditionPattern,
				CONS_WID2("node", "condition"), true ) ? 0 : 1;

		error += configure(theFORMAT, mNodeTimedConditionPattern,
				CONS_WID2("node#timed", "condition"), true ) ? 0 : 1;


		error += configure(theFORMAT, mTimePattern    , "time"    ) ? 0 : 1;
		error += configure(theFORMAT, mAssignPattern  , "assign"  ) ? 0 : 1;
		error += configure(theFORMAT, mNewfreshPattern, "newfresh") ? 0 : 1;

		error += configure(theFORMAT, mInputPattern , "input" ) ? 0 : 1;
		error += configure(theFORMAT, mOutputPattern, "output") ? 0 : 1;


		error += configure(theFORMAT, mInputEnvPattern,
				CONS_WID2("input", "env"), true ) ? 0 : 1;

		error += configure(theFORMAT, mOutputEnvPattern,
				CONS_WID2("output", "env"), true) ? 0 : 1;


		error += configure(theFORMAT, mInputRdvPattern,
				CONS_WID2("input", "rdv"), true ) ? 0 : 1;

		error += configure(theFORMAT, mOutputRdvPattern,
				CONS_WID2("output", "rdv"), true) ? 0 : 1;


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

		error += configure(theFORMAT, mLifelineStatePattern,
				CONS_WID2("lifeline", "state"), true ) ? 0 : 1;

		error += configure(theFORMAT, mStateKindPattern,
				CONS_WID2("state", "kind"), true ) ? 0 : 1;

		error += configure(theFORMAT,
				mMachinePattern   , "machine"   ) ? 0 : 1;

		error += configure(theFORMAT,
				mStatemachinePattern, "statemachine" ) ? 0 : 1;
		error += configure(theFORMAT,
				mStatePattern, "state" ) ? 0 : 1;

		error += configure(theFORMAT,
				mTransitionPattern, "transition") ? 0 : 1;

		error += configure(theFORMAT,
				mRoutinePattern   , "routine"   ) ? 0 : 1;

		error += configure(theFORMAT,
				mRunnablePattern  , "runnable"  ) ? 0 : 1;

		error += configure(theFORMAT, mExecutionInformationPattern ,
			ENUM_TRACE_POINT::ATTRIBUTE_EXECUTION_INFORMATION_ID, true ) ? 0 : 1;

		error += configure(theFORMAT, mMetaTracePattern  , "trace"  ) ? 0 : 1;
		error += configure(theFORMAT, mMetaDebugPattern  , "debug"  ) ? 0 : 1;

		return( error == 0 );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////////

void SequenceDiagramTraceFormatter::formatHeader(OutStream & os)
{
	os.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	// En tête global
	boost::format headformatter(mFileHeaderPattern);
	headformatter.exceptions( boost::io::no_error_bits );
	os << headformatter << std::flush;

	boost::format beginformatter(mFileBeginPattern);
	beginformatter.exceptions( boost::io::no_error_bits );
	os << beginformatter << std::flush;

	formatBoxHeader( os );
	{
		//!! NOTHING
	}

	formatParticipant( os );

	boost::format endBoxFormatter(mBoxEndPattern);
	endBoxFormatter.exceptions( boost::io::no_error_bits );
	os << endBoxFormatter << std::flush;
}

void SequenceDiagramTraceFormatter::formatTrace(
		OutStream & os, const TraceSequence & aTraceElement)
{
	formatTraceID(os, aTraceElement, mPathHeaderPattern);
	formatTraceID(os, aTraceElement, mPathBeginPattern);

	mTraceSequence = (& aTraceElement);

	if( mPrintLifelines )
	{
		formatLifelines(os, aTraceElement);
		os << std::endl;
	}
	else
	{
		format(os, aTraceElement);
	}

	formatTraceID(os, aTraceElement, mPathEndPattern);
}

void SequenceDiagramTraceFormatter::formatFooter(OutStream & os)
{
	boost::format endformatter(mFileEndPattern);
	endformatter.exceptions( boost::io::no_error_bits );
	os << endformatter << std::flush;

	os.restoreSymbexValueCSS();
}


/**
 *
 */
void SequenceDiagramTraceFormatter::formatBoxHeader(OutStream & out)
{
	std::string strNameSystem =
			mTraceGenerator.getConfiguration().getExecutableSystem().getPortableNameID();

	boost::format formatter( mBoxHeaderPattern );
	formatter.exceptions( boost::io::no_error_bits );
	out << formatter
			% strNameSystem;
}



/**
 *
 */
void SequenceDiagramTraceFormatter::formatParticipant(OutStream & out)
{
	const sep::TableOfRuntimeT & tableOfMachines = mTraceGenerator.
			getConfiguration().getMainExecutionData().getTableOfRuntime();

	std::list< const RuntimeForm * > aListOfParticipants;
	std::list< const RuntimeForm * > aListOfAlternativeParticipants;

	for( const auto & machine : tableOfMachines )
	{
		if ( machine->getExecutable()->isCommunicator() )
		{
			if( not machine->getExecutable()->getSpecifier().isComponentSystem() )
			{
				aListOfAlternativeParticipants.push_back( machine );
			}

			if ( machine->getExecutable()->getSpecifier().hasFeatureLifeline() )
			{
				aListOfParticipants.push_back( machine );
			}
		}
	}

	if( aListOfParticipants.empty() )
	{
		aListOfParticipants.splice(
				aListOfParticipants.end(), aListOfAlternativeParticipants );
	}

	for( const auto & machine : aListOfParticipants )
	{

		boost::format formatter( mParticipantPattern );
		formatter.exceptions( boost::io::no_error_bits );

		std::string participantID =
				formatLifelineId(machine->getRID(), mLifelineIdPattern);

		std::string strParticipant = (OSS() <<  "\"" <<
				machine->getInstance()->getUnrestrictedName()
				<< "\" as " << participantID);

		mListOfParticipants.push_back( participantID );

		out << formatter
				% strParticipant;
	}

}


////////////////////////////////////////////////////////////////////////////////
// LIFELINE API
////////////////////////////////////////////////////////////////////////////////

/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> ( machine ) identifier
 */
std::string SequenceDiagramTraceFormatter::formatLifelineId(
		const RuntimeID & aLifeline, const std::string & pattern)
{
	if( aLifeline.valid() )
	{
		StringOutStream oss;

		boost::format formatter(pattern);
		formatter.exceptions( boost::io::no_error_bits );

		oss << formatter
				% aLifeline.strPid()
				% (aLifeline.hasParent() ?
						aLifeline.getParent().getPortableNameID() : "")
				% aLifeline.getPortableNameID()
				<< std::flush;

		return( oss.str() );
	}
	else
	{
		return( RuntimeLib::RID_ENVIRONMENT.getPortableNameID() );
	}
}


void SequenceDiagramTraceFormatter::formatLifelines(
		OutStream & os, const TraceSequence & aTraceElt)
{
	RuntimeQuery RQuery( mTraceGenerator.getConfiguration() );

	Vector< RuntimeID > lifelines;
	RQuery.getSystemLifelines(lifelines);

	Vector< RuntimeID >::iterator itLifelineRID = lifelines.begin();
	Vector< RuntimeID >::iterator endLifeline = lifelines.end();
	for( ; itLifelineRID != endLifeline ; ++itLifelineRID)
	{
		TraceSequence lifelineTrace(aTraceElt.mEC, 0);

		if( toLifeline( aTraceElt, lifelineTrace, *itLifelineRID ) > 0 )
		{
			formatLifelineID(os, *itLifelineRID, mLifelineHeaderPattern);
			formatLifelineID(os, *itLifelineRID, mLifelineBeginPattern);

			format(os, lifelineTrace);

			formatLifelineID(os, *itLifelineRID, mLifelineEndPattern);
		}
	}
}

std::size_t SequenceDiagramTraceFormatter::toLifeline(
		const TraceSequence & lifelineInput,
		TraceSequence & lifelineTrace,
		const RuntimeID & lifelineRID) const
{
	std::size_t lifelineSize = 0;

	TracePoint * currentTracePoint = nullptr;
	TracePoint * lifelineIOPoint = nullptr;

	for( const auto & itPoint : lifelineInput.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			currentTracePoint = itPoint.to_ptr< TracePoint >();

			// Tester si itPoint appartient à la ligne de vie lifelineRID
			if( lifelineContains(lifelineRID, *currentTracePoint) )
			{
				if( currentTracePoint->isComInput() )
				{
					lifelineIOPoint = new TracePoint( *currentTracePoint );
					lifelineIOPoint->op = AVM_OPCODE_INPUT_ENV;

					lifelineTrace.append( BF( lifelineIOPoint ) );
					++lifelineSize;
				}
				else if( currentTracePoint->isComOutput() )
				{
					lifelineIOPoint = new TracePoint( *currentTracePoint );
					lifelineIOPoint->op = AVM_OPCODE_OUTPUT_ENV;

					lifelineTrace.append( BF( lifelineIOPoint ) );
					++lifelineSize;
				}
				else
				{
					lifelineTrace.append( itPoint );
					++lifelineSize;
				}
			}
		}
		else if( itPoint.is< TraceSequence >() )
		{
			lifelineSize += toLifeline( itPoint.to< TraceSequence >(),
					lifelineTrace, lifelineRID );
		}
	}

	return( lifelineSize );
}


bool SequenceDiagramTraceFormatter::lifelineContains(
		const RuntimeID & lifelineRID, const TracePoint & aPoint) const
{
	if( aPoint.RID.valid() && lifelineRID.isAncestorOf( aPoint.RID ) )
	{
		return( true );
	}
	else if( aPoint.config.isnotNullref()
			&& lifelineRID.isAncestorOf( aPoint.config.getRuntimeID() ) )
	{
		return( true );
	}
	else if( aPoint.isNodeCondition() && aPoint.EC.isnotNullref()
			&& aPoint.EC.hasRunnableElementTrace() ) {
		return lifelineContains(lifelineRID, aPoint.EC.getRunnableElementTrace());
	}

	return( false );
}


bool SequenceDiagramTraceFormatter::lifelineContains(
		const RuntimeID & lifelineRID, const BF & aRunTrace) const
{
	if( aRunTrace.invalid() )
	{
		return( false );
	}
	else if( aRunTrace.is< ExecutionConfiguration >() )
	{
		return( lifelineRID.isAncestorOf(
				aRunTrace.to< ExecutionConfiguration >().getRuntimeID()) );
	}
	else if( aRunTrace.is< AvmCode >()
			&& OperatorManager::isSchedule( aRunTrace.to< AvmCode >().getOperator() ) )
	{
		for( const auto & itOperand : aRunTrace.to< AvmCode >().getOperands() )
		{
			if( lifelineContains(lifelineRID, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


/**
 * EXECUTION CONTEXT HEADER
 * %1% --> ec#id
 * %2% --> ec#eval
 * %3% --> ec#hight
 * %4% --> ec#width
 * %5% --> ec#weight
 * %6% --> statemachine configuration i.e. control node
 */
std::string SequenceDiagramTraceFormatter::strFormatExecutionContextUfid(
		const ExecutionContext & anEC)
{
	if( anEC.isnotNullref() )
	{
		StringOutStream oss;

		boost::format formatter(mExecutionContextUfidPattern);
		formatter.exceptions( boost::io::no_error_bits );

		oss << formatter
				% anEC.getIdNumber()
				% anEC.getEvalNumber()
				% anEC.getHeight()
				% anEC.getWidth()
				% anEC.getWeight()
				% anEC.getExecutionData().strStateConf(mLifelineStatePattern);

		return( oss.str() );
	}

	return( "ctx<null>" );
}


void SequenceDiagramTraceFormatter::formatTraceID(OutStream & os,
		const TraceSequence & aTraceElt, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% aTraceElt.tid
			% strFormatExecutionContextUfid(
					ExecutionContext::REF( aTraceElt.mEC ) )
			<< std::flush;
}


void SequenceDiagramTraceFormatter::formatLifelineID(OutStream & os,
		const RuntimeID & aLifeline, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% aLifeline.strPid()
			% (aLifeline.hasParent() ? aLifeline.getParent().getPortableNameID() : "")
			% aLifeline.getPortableNameID()
			<< std::flush;
}


void SequenceDiagramTraceFormatter::formatString(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% ( aTracePoint.value.valid() ?
			aTracePoint.value.as_ptr< String >()->getValue() : "" )
			% strFormatExecutionContextUfid( aTracePoint.EC );
}


void SequenceDiagramTraceFormatter::formatStep(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% ( aTracePoint.value.valid() ? aTracePoint.value.as_ptr<
					String >()->getValue() : "" )
			% strFormatExecutionContextUfid( aTracePoint.EC );
}


void SequenceDiagramTraceFormatter::format(OutStream & os, const TraceSequence & aTraceElt)
{
	for( const auto & itPoint : aTraceElt.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			format(os, itPoint.to< TracePoint >());
		}

		else if( itPoint.is< TraceSequence >() )
		{
			format(os, itPoint.to< TraceSequence >());
		}
	}
}

void SequenceDiagramTraceFormatter::format(OutStream & os, const TracePoint & aTracePoint)
{
	switch( aTracePoint.nature )
	{
		case ENUM_TRACE_POINT::TRACE_COMMENT_NATURE:
		{
			formatString(os, aTracePoint, mCommentPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_SEPARATOR_NATURE:
		{
			formatString(os, aTracePoint, mSeparatorPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_NEWLINE_NATURE:
		{
			formatString(os, aTracePoint, mNewlinePattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_STEP_HEADER_NATURE:
		{
			formatStep(os, aTracePoint, mStepHeaderPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_STEP_BEGIN_NATURE:
		{
			formatStep(os, aTracePoint, mStepBeginPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_STEP_END_NATURE:
		{
			formatStep(os, aTracePoint, mStepEndPattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_INIT_HEADER_NATURE:
		{
			formatStep(os, aTracePoint, mInitializationHeaderPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_INIT_BEGIN_NATURE:
		{
			formatStep(os, aTracePoint, mInitializationBeginPattern);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_INIT_END_NATURE:
		{
			formatStep(os, aTracePoint, mInitializationEndPattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_EXECUTION_INFORMATION_NATURE:
		{
			formatExecutionInformation(os, aTracePoint,
					mExecutionInformationPattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		{
			formatCondition(os, mPathConditionPattern,
					aTracePoint);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:
		{
			formatCondition(os, mPathTimedConditionPattern,
					aTracePoint);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		{
			formatNodeCondition(os, mNodeConditionPattern,
					aTracePoint);

			break;
		}
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:
		{
			formatNodeCondition(os, mNodeTimedConditionPattern,
					aTracePoint);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_BUFFER_NATURE:
		{
			formatBuffer(os, aTracePoint, mAssignPattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_META_TRACE_NATURE:
		{
			formatMetaElement(os, aTracePoint, mMetaTracePattern);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_META_DEBUG_NATURE:
		{
			formatMetaElement(os, aTracePoint, mMetaDebugPattern);

			break;
		}

		default:
		{
			switch( aTracePoint.op )
			{
				case AVM_OPCODE_TIMED_GUARD:
				{
					format(os, aTracePoint, mTimePattern);
					break;
				}

				case AVM_OPCODE_ASSIGN:
				{
					formatAssign(os, aTracePoint, mAssignPattern);
					break;
				}

				case AVM_OPCODE_ASSIGN_NEWFRESH:
				{
					format(os, aTracePoint, mNewfreshPattern);
					break;
				}

				case AVM_OPCODE_INPUT:
				{
					formatIO(os, aTracePoint, mInputPattern);
					break;
				}
				case AVM_OPCODE_INPUT_FROM:
				{
					formatIO(os, aTracePoint, mInputPattern);
					break;
				}
				case AVM_OPCODE_INPUT_ENV:
				{
					formatIO(os, aTracePoint, mInputEnvPattern);
					break;
				}
				case AVM_OPCODE_INPUT_RDV:
				{
//					formatIO(os, aTracePoint, mInputRdvPattern);
					break;
				}

				case AVM_OPCODE_OUTPUT:
				{
					formatOutput( os, aTracePoint, mOutputPattern );

					break;
				}
				case AVM_OPCODE_OUTPUT_TO:
				{
					formatIO(os, aTracePoint, mOutputPattern);
					break;
				}
				case AVM_OPCODE_OUTPUT_ENV:
				{
					formatIO(os, aTracePoint, mOutputEnvPattern);
					break;
				}
				case AVM_OPCODE_OUTPUT_RDV:
				{
					formatOutput( os, aTracePoint, mOutputRdvPattern );

					break;
				}


				case AVM_OPCODE_RUN:
				{
					const Specifier & specifier = aTracePoint.object
							->as< InstanceOfMachine >().getSpecifier();

					if( specifier.isFamilyComponentState() )
					{
						format(os, aTracePoint, mStatePattern);
					}
					else if( specifier.isFamilyComponentStatemachine()
							&& specifier.isMocStateTransitionStructure() )
					{
						format(os, aTracePoint, mStatemachinePattern);
					}
					else
					{
						format(os, aTracePoint, mMachinePattern);
					}
					break;
				}

				case AVM_OPCODE_INVOKE_TRANSITION:
				{
					format(os, aTracePoint, mTransitionPattern);
					break;
				}

				case AVM_OPCODE_INVOKE_ROUTINE:
				{
					format(os, aTracePoint, mRoutinePattern);
					break;
				}

				default:
				{
					switch( aTracePoint.nature )
					{
						case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
						case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
						case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
						{
							format(os, aTracePoint, mMachinePattern);

							break;
						}
						case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
						{
							format(os, aTracePoint, mTransitionPattern);

							break;
						}
						case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:
						{
							format(os, aTracePoint, mRoutinePattern);

							break;
						}

						case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:
						{
							format(os, aTracePoint, mRunnablePattern);

							break;
						}

						default:
						{
							aTracePoint.toStream(os);

							break;
						}
					}

					break;
				}
			}
			break;
		}
	}
}


void SequenceDiagramTraceFormatter::formatOutput(OutStream & os,
		const TracePoint & aTracePoint, const std::string & outputPattern)
{
	if( aTracePoint.config.isnotNullref() && aTracePoint.config.hasIOMessage() )
	{
		const Message & ioMessage = aTracePoint.config.getIOMessage();

		const auto ite = mMapMessageReceiver.find( ioMessage.raw_pointer() );

		if( ite != mMapMessageReceiver.end() )
		{
			formatOutput( os, aTracePoint, outputPattern, (*ite).second );
		}
		else
		{
			List< RuntimeID > listRIDOfReceivers;

			if( mTraceSequence != nullptr )
			{
				collectRuntimeReceiver(*mTraceSequence, ioMessage, listRIDOfReceivers);
			}

			if( listRIDOfReceivers.empty() && ioMessage.hasRoutingData() )
			{
				const InstanceOfConnector & aConnector =
						ioMessage.getRoutingData().getConnector();
				bool isReflexive = false;

				for( const auto & itRoutingData : aConnector.getInputRoutingDataTable() )
				{
					if( aTracePoint.object != &( itRoutingData.getPort() ) )
					{
						listRIDOfReceivers.append(
								aTracePoint.EC.getExecutionData().getRuntimeID(
										itRoutingData.getMachine() ) );
					}
					else
					{
						isReflexive = true;
					}
				}

				if( listRIDOfReceivers.empty() && isReflexive )
				{
					listRIDOfReceivers.append(
							aTracePoint.EC.getExecutionData().getRuntimeID(
									*( aTracePoint.machine )) );
				}
			}

			if( listRIDOfReceivers.nonempty() )
			{
				formatOutput( os, aTracePoint, outputPattern, listRIDOfReceivers );
			}
		}
	}
}


void SequenceDiagramTraceFormatter::collectRuntimeReceiver(
		const TraceSequence & aTraceSequence, const Message & ioMessage,
		List< RuntimeID > & aListOfReceiverRID )
{
	for( const auto & itPoint : aTraceSequence.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			const TracePoint & aTracePoint = itPoint.to< TracePoint >();
			if( aTracePoint.isComInput()
				&& aTracePoint.config.isnotNullref()
				&& (aTracePoint.config.getIOMessage() == ioMessage) )
			{
				aListOfReceiverRID.append( aTracePoint.RID );
			}
		}

		else if( itPoint.is< TraceSequence >() )
		{
			collectRuntimeReceiver(itPoint.to< TraceSequence >(),
					ioMessage, aListOfReceiverRID);
		}
	}

}


void SequenceDiagramTraceFormatter::format(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	std::string strLifeline = "<<unknown>>";

	strLifeline = aTracePoint.RID.getLifeline().getInstance()->getPortableNameID();

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	ossValue.str("");
	ossValue.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	aTracePoint.formatValueStream( ossValue );

	os << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% strLifeline
			% aTracePoint.machine->getPortableNameID()
			% aTracePoint.object->getPortableNameID()
			% ossValue.str();

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << "' ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


void SequenceDiagramTraceFormatter::formatIO(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	int indexOfMessage;

	bool incrementIndex = false;
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	ossValue.str("");
	ossValue.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	aTracePoint.formatValueStream( ossValue );

	std::string sender = "";
	std::string receiver = "NO_RECEIVER";
	std::string colorOfMessage = "";
	std::string timestamp = "$timestamp";

//	if ( aTracePoint.op == AVM_OPCODE_OUTPUT_ENV )
//	{
//		sender = aTracePoint.RID.getLifeline().getInstance()->getPortableNameID();
//	}
//	else if ( aTracePoint.op == AVM_OPCODE_INPUT_ENV )
//	{
//		receiver = aTracePoint.RID.getLifeline().getInstance()->getPortableNameID();
//	}

	if( aTracePoint.isComInput() )
	{
		receiver = formatLifelineId(
				aTracePoint.RID.getLifeline(), mLifelineIdPattern);
	}
	else
	{
		sender = formatLifelineId(
				aTracePoint.RID.getLifeline(), mLifelineIdPattern);
	}

	if( aTracePoint.config.isnotNullref()
			&& aTracePoint.config.hasIOMessage() )
	{
		const Message & ioMessage = aTracePoint.config.getIOMessage();
		if( ioMessage.hasSenderRID() )
		{
			sender = formatLifelineId(
					ioMessage.getSenderRID().getLifeline(),
					mLifelineIdPattern);
		}

		if( ioMessage.hasReceiverRID() && receiver.empty() )
		{
			receiver = formatLifelineId(
					ioMessage.getReceiverRID().getLifeline(),
					mLifelineIdPattern);
		}

		if ( aTracePoint.op == AVM_OPCODE_INPUT  )
		{
//			receiver = formatLifelineId(
//					aTracePoint.RID.getLifeline(), mLifelineIdPattern);

			for (const auto & pair : mMapOfLifelineAndId )
			{
				if ( ioMessage == pair.first )
				{
					indexOfMessage = pair.second;
				}
			}
		}
//		else if ( aTracePoint.op == AVM_OPCODE_OUTPUT )
//		{
//			mMapOfLifelineAndId.append(std::make_pair( ioMessage, mIndexOfMessageInMap ));
//
//			indexOfMessage = mIndexOfMessageInMap;
//
//			incrementIndex = true;
//		}

		colorOfMessage = mMapOfColors[indexOfMessage % mMapOfColors.size()];
	}

	if( aTracePoint.config.isnotNullref()
		&& aTracePoint.config.hasTimestamp() )
	{
		timestamp = aTracePoint.config.getTimestamp().str();
	}

	mWrapData.SEPARATOR = "\\n<font color = " + colorOfMessage + ">";

	os << mWrapData << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getPortableNameID()
			% aTracePoint.object->getPortableNameID()
			% ossValue.str()
			% sender
			% receiver
			% indexOfMessage
			% colorOfMessage
			% timestamp;

	os << END_WRAP;

	mWrapData.SEPARATOR = mWrapDataSeparator;

	if ( incrementIndex ){
		mIndexOfMessageInMap++;
	}

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << "' ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


void SequenceDiagramTraceFormatter::formatOutput(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern,
		List< RuntimeID > aListOfReceiverRID )
{
	int indexOfMessage;
	bool incrementIndex = false;
	std::string sender = "";
	std::string receiver = "NO_RECEIVER";
	std::string colorOfMessage = "";
	std::string timestamp = "$timestamp";
	std::string blackColor = "#000000";

	if( aTracePoint.config.isnotNullref()
		&& aTracePoint.config.hasTimestamp() )
	{
		timestamp = aTracePoint.config.getTimestamp().str();
	}

	const Message & ioMessage = aTracePoint.config.getIOMessage();

	// formatter
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	ossValue.str("");
	ossValue.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	aTracePoint.formatValueStream( ossValue );

	if ( aListOfReceiverRID.nonempty() )
	{
		for ( const auto & aRID : aListOfReceiverRID )
		{
			ioMessage.setReceiverRID( aRID );

			if( ioMessage.hasSenderRID() )
			{
				sender = formatLifelineId(
						ioMessage.getSenderRID().getLifeline(),
						mLifelineIdPattern);
			}

			receiver = formatLifelineId(aRID.getLifeline(), mLifelineIdPattern);

			mMapOfLifelineAndId.append(std::make_pair( ioMessage, mIndexOfMessageInMap ));

			indexOfMessage = mIndexOfMessageInMap;

			colorOfMessage = mMapOfColors[indexOfMessage % mMapOfColors.size()];

			mWrapData.SEPARATOR = "\\n<font color = " + colorOfMessage + ">";

			std::size_t  LINE_WIDTH_SAVE = mWrapData.LINE_WIDTH + sender.size();
			mWrapData.LINE_WIDTH += sender.size() + receiver.size() + 13;


			os << mWrapData << formatter
					% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
					% aTracePoint.machine->getPortableNameID()
					% aTracePoint.object->getPortableNameID()
					% ossValue.str()
					% sender
					% receiver
					% indexOfMessage
					% colorOfMessage
					% timestamp;

			os << END_WRAP;

			mWrapData.SEPARATOR = mWrapDataSeparator;

			mWrapData.LINE_WIDTH = LINE_WIDTH_SAVE;

		}

		incrementIndex = true;

		if ( incrementIndex ){
			mIndexOfMessageInMap++;
		}
	}
	else
	{
		sender = formatLifelineId(
				ioMessage.getSenderRID().getLifeline(),
				mLifelineIdPattern);

		receiver = "";

		os << mWrapData << formatter
				% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
				% aTracePoint.machine->getPortableNameID()
				% aTracePoint.object->getPortableNameID()
				% ossValue.str()
				% sender
				% receiver
				% indexOfMessage
				% blackColor
				% timestamp;

		os << END_WRAP;

		mWrapData.SEPARATOR = mWrapDataSeparator;

	}
}


/**
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> buffer identifier
 * %4% --> value
 */
void SequenceDiagramTraceFormatter::formatBuffer(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	const BaseBufferForm & aBufferValue =
			aTracePoint.value.to< BaseBufferForm >();
	OSS oss( AVM_STR_INDENT , os );
	aBufferValue.toStreamValue( oss << IGNORE_FIRST_TAB );

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getPortableNameID()
			% aTracePoint.object->getPortableNameID()
			% oss.str();

	os << END_WRAP;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << "' ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


/**
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
void SequenceDiagramTraceFormatter::formatAssign(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
//	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
//			<< "TracePoint::object !!!"
//			<< SEND_EXIT;

	mWrapData.SEPARATOR = "\n ";

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	if( aTracePoint.object == nullptr )
	{
		if( aTracePoint.value.is< ArrayBF >() )
		{
			const ArrayBF & array = aTracePoint.value.as< ArrayBF >();

			for( std::size_t offset = 0 ; offset < array.size() ; ++offset )
			{
				const TracePoint & assignTracePoint = array[offset].to< TracePoint >();

				OSS oss( AVM_STR_INDENT , os );
				assignTracePoint.formatValueStream( oss << IGNORE_FIRST_TAB );

				os << mWrapData << formatter
						% (assignTracePoint.RID.valid() ? assignTracePoint.RID.strPid() : "<pid#?>")
						% assignTracePoint.machine->getPortableNameID()
						% assignTracePoint.object->getPortableNameID()
						% oss.str();
				os << END_WRAP;
			}
		}
		else
		{
			os << mWrapData << formatter
					% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
					% aTracePoint.machine->getPortableNameID()
					% aTracePoint.object->getPortableNameID()
					% aTracePoint.value.str();
			os << END_WRAP;
		}
	}
	else
	{
		OSS oss( AVM_STR_INDENT , os );
		aTracePoint.formatValueStream( oss << IGNORE_FIRST_TAB );

		os << mWrapData << formatter
				% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
				% aTracePoint.machine->getPortableNameID()
				% aTracePoint.object->getPortableNameID()
				% oss.str();
		os << END_WRAP;
	}


	mWrapData.SEPARATOR = mWrapDataSeparator;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << "' ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


/**
 * DATA
 * [ Timed ] Path Condition
 * Assignment: var = value
 */
void SequenceDiagramTraceFormatter::formatCondition(OutStream & os,
		const std::string & formatPattern,  const TracePoint & aTracePoint)
{
	const BF & aCode = aTracePoint.value;

	const std::string & firstParticipant = mListOfParticipants.front();

	const std::string & lastParticipant = mListOfParticipants.back();

	RuntimeID aRid = getLifelineRuntimeID( aTracePoint.EC.getRunnableElementTrace() );

	const std::string & strLifeline = aRid.valid()
			? aRid.getLifeline().getInstance()->getPortableNameID()
			: firstParticipant; // "null<lifeline>";

	boost::format formatter(formatPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << " " << formatter
			% aCode.str()
			% strLifeline
			% firstParticipant
			% lastParticipant;

	os << END_WRAP;
}

/**
 * EXECUTION INFORMATION
 * Info: ID = value
 */

void SequenceDiagramTraceFormatter::formatExecutionInformation(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter % aTracePoint.value.str();

	os << END_WRAP;
}


/**
 * %1% --> condition string
 * %2% --> name of lifeline
 */
void SequenceDiagramTraceFormatter::formatNodeCondition( OutStream & os,
		const std::string & formatPattern, const TracePoint & aTracePoint )
{
	const BF & aCode = aTracePoint.value;

	boost::format formatter(formatPattern);
	formatter.exceptions( boost::io::no_error_bits );

	RuntimeID aRid = getLifelineRuntimeID( aTracePoint.EC.getRunnableElementTrace() );
		
	const std::string & strLifeline = aRid.valid()
			? aRid.getLifeline().getInstance()->getPortableNameID()
			: mListOfParticipants.front(); // "null<lifeline>"

	os << mWrapData << " " << formatter
			% aCode.str()
			% strLifeline;

	os << END_WRAP;
}


/**
 * META ELEMENT
 * @trace{ ... }
 * @debug{ ... }
 * @informal{ ... }
* %1% --> machine runtime pid
* %2% --> machine container identifier
* %3% --> object
* %4% --> value
*/
void SequenceDiagramTraceFormatter::formatMetaElement(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	bool saveFlag = String::ENABLE_QUOTE_PRINTING;

	String::ENABLE_QUOTE_PRINTING = false;

	ossValue.str("");
	ossValue.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	aTracePoint.formatValueStream( ossValue );

	String::ENABLE_QUOTE_PRINTING = saveFlag;

	std::string strValue = ossValue.str();
	StringTools::replaceAllEscapeSequences(strValue);

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getPortableNameID()
			% aTracePoint.object->getPortableNameID()
			% strValue;

	os << END_WRAP;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << "' ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}



RuntimeID SequenceDiagramTraceFormatter::getLifelineRuntimeID(const BF & aRunTrace) const
{
	if( aRunTrace.invalid() )
	{
		return( RuntimeID::nullref() );
	}
	else if( aRunTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf = aRunTrace.to< ExecutionConfiguration >();

		if( aConf.getRuntimeID().getExecutable()->isLifeline() ) //isWeakLifeline() )
		{
			return( aConf.getRuntimeID() );
		}
		else if( (aConf.isRunnableState() || aConf.isTransition())
			&& aConf.getRuntimeID().hasLifeline() )
		{
			return( aConf.getRuntimeID().getLifeline() );
		}
	}
	else if( aRunTrace.is< AvmCode >()
			&& OperatorManager::isSchedule( aRunTrace.to< AvmCode >().getOperator() ) )
	{
		for( const auto & itOperand : aRunTrace.to< AvmCode >().getOperands() )
		{
			const RuntimeID & RID = getLifelineRuntimeID( itOperand );

			if( RID.valid() )
			{
				return( RID );
			}
		}
	}

	return( RuntimeID::nullref() );
}



} /* namespace sep */
