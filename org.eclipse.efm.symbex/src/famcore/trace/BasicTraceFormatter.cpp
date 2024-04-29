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
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BasicTraceFormatter.h"

#include "TraceManager.h"

#include <common/SerializerFeature.h>

#include  <famcore/trace/AvmTraceGenerator.h>

#include <fml/executable/InstanceOfMachine.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/RuntimeLib.h>
#include <fml/runtime/RuntimeQuery.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <boost/format.hpp>


namespace sep
{


/**
 * ASSIGN
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & BasicTraceFormatter::
DEFAULT_ASSIGN_PATTERN = "\t%2%:%3% = %4%\n";

/**
 * NEWFRESH
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> variable identifier
 * %4% --> value
 */
const std::string & BasicTraceFormatter::
DEFAULT_NEWFRESH_PATTERN = "\tnewfresh %2%->%3%( %4% )\n";

/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> ( port | signal ) identifier
 * %4% --> value
 * %5% --> machine sender   identifier name
 * %6% --> machine receiver identifier name
 */
const std::string & BasicTraceFormatter::
DEFAULT_INPUT_PATTERN = "\tinput  %2%->%3%%4%\n";

const std::string & BasicTraceFormatter::
DEFAULT_OUTPUT_PATTERN = "\toutput %2%->%3%%4%\n";


const std::string & BasicTraceFormatter::
DEFAULT_INPUT_ENV_PATTERN = "\tinput#env  %2%->%3%%4%\n";

const std::string & BasicTraceFormatter::
DEFAULT_OUTPUT_ENV_PATTERN = "\toutput#env %2%->%3%%4%\n";


const std::string & BasicTraceFormatter::
DEFAULT_INPUT_RDV_PATTERN = "\tinput#rdv  %2%->%3%%4%\n";

const std::string & BasicTraceFormatter::
DEFAULT_OUTPUT_RDV_PATTERN = "\toutput#rdv %2%->%3%%4%\n";

/**
 * MACHINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> machine identifier
 */
const std::string & BasicTraceFormatter::
DEFAULT_MACHINE_PATTERN = "%3%";

/**
 * TRANSITION
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> transition identifier
 */
const std::string & BasicTraceFormatter::
DEFAULT_TRANSITION_PATTERN = "%2%->%3%";

/**
 * ROUTINE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> routine identifier
 */
const std::string & BasicTraceFormatter::
DEFAULT_ROUTINE_PATTERN = "%2%->%3%";


/**
 * META TRACE
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> object identifier
 * %4% --> value as operand toString
 */
const std::string & BasicTraceFormatter::
DEFAULT_META_TRACE_PATTERN = "%4%";

/**
 * META DEBUG
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> object identifier
 * %4% --> operand
 */
const std::string & BasicTraceFormatter::
DEFAULT_META_DEBUG_PATTERN = "%4%";


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

bool BasicTraceFormatter::configure(const WObject * FORMAT,
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

bool BasicTraceFormatter::configureImpl(const WObject * wfParameterObject)
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

		error += configure(theFORMAT, mExecutionContextUfidPattern,
				OR_WID2(CONS_WID3("execution", "context", "(qn|uf)?id"),
						CONS_WID2("context", "(qn|uf)?id")), true) ? 0 : 1;

		error += configure(theFORMAT, mFileHeaderPattern,
				CONS_WID2("file", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mFileBeginPattern,
				CONS_WID2("file", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mFileEndPattern,
				CONS_WID2("file", "end"), true   ) ? 0 : 1;


		error += configure(theFORMAT, mTestcaseHeaderPattern,
				CONS_WID2("testcase", "header"), true) ? 0 : 1;

		error += configure(theFORMAT, mTestcaseBeginPattern,
				CONS_WID2("testcase", "begin"), true ) ? 0 : 1;

		error += configure(theFORMAT, mTestcaseEndPattern,
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

void BasicTraceFormatter::formatHeader(OutStream & os)
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
}

void BasicTraceFormatter::formatTrace(OutStream & os, const TraceSequence & aTraceElt)
{
	formatTraceID(os, aTraceElt, mTestcaseHeaderPattern);
	formatTraceID(os, aTraceElt, mTestcaseBeginPattern);

	format(os, aTraceElt);

	formatTraceID(os, aTraceElt, mTestcaseEndPattern);

	if( mPrintLifelines )
	{
		formatLifelines(os, aTraceElt);
		os << std::endl;
	}
}

void BasicTraceFormatter::formatFooter(OutStream & os)
{
	boost::format endformatter(mFileEndPattern);
	endformatter.exceptions( boost::io::no_error_bits );
	os << endformatter << std::flush;

	os.restoreSymbexValueCSS();
}



void BasicTraceFormatter::formatLifelines(
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

		if( aTraceElt.toLifeline(lifelineTrace, *itLifelineRID) > 0 )
		{
			formatLifelineID(os, *itLifelineRID, mLifelineHeaderPattern);
			formatLifelineID(os, *itLifelineRID, mLifelineBeginPattern);

			format(os, lifelineTrace);

			formatLifelineID(os, *itLifelineRID, mLifelineEndPattern);
		}
	}
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
std::string BasicTraceFormatter::strFormatExecutionContextUfid(
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


void BasicTraceFormatter::formatTraceID(OutStream & os,
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


void BasicTraceFormatter::formatLifelineID(OutStream & os,
		const RuntimeID & aLifeline, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% aLifeline.strPid()
			% (aLifeline.hasParent() ? aLifeline.getParent().getNameID() : "")
			% aLifeline.getNameID()
			<< std::flush;
}


void BasicTraceFormatter::formatString(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% ( aTracePoint.value.valid() ?
			aTracePoint.value.as_ptr< String >()->getValue() : "" )
			% strFormatExecutionContextUfid( aTracePoint.EC );
}


void BasicTraceFormatter::formatStep(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% ( aTracePoint.value.valid() ? aTracePoint.value.as_ptr<
					String >()->getValue() : "" )
			% strFormatExecutionContextUfid( aTracePoint.EC );
}


void BasicTraceFormatter::format(OutStream & os, const TraceSequence & aTraceElt)
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

void BasicTraceFormatter::format(OutStream & os, const TracePoint & aTracePoint)
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
			dotFormatCondition(os, mPathConditionPattern,
					aTracePoint.value);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:
		{
			dotFormatCondition(os, mPathTimedConditionPattern,
					aTracePoint.value);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		{
			dotFormatCondition(os, mNodeConditionPattern,
					aTracePoint.value);

			break;
		}

		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:
		{
			dotFormatCondition(os, mNodeTimedConditionPattern,
					aTracePoint.value);

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
					wrap_format(os, aTracePoint, mAssignPattern);
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
					formatIO(os, aTracePoint, mInputRdvPattern);
					break;
				}

				case AVM_OPCODE_OUTPUT:
				{
					formatIO(os, aTracePoint, mOutputPattern);
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
					formatIO(os, aTracePoint, mOutputRdvPattern);
					break;
				}


				case AVM_OPCODE_RUN:
				{
					const Specifier & specifier = aTracePoint.object
							->as< InstanceOfMachine >().getSpecifier();
//
//					const Specifier & specifier =
//							aTracePoint.config.getRuntimeID().getSpecifier();
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


void BasicTraceFormatter::format(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );
//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	ossValue.str("");
	ossValue.setSymbexValueCSS( os );

	aTracePoint.formatValueStream( ossValue );

	os << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getNameID()
			% aTracePoint.object->getNameID()
			% ossValue.str();

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << " ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


/**
 * INPUT / OUTPUT
 * %1% --> machine runtime pid
 * %2% --> machine container identifier
 * %3% --> ( port | signal ) identifier
 * %4% --> value
 * %5% --> machine sender   identifier name
 * %6% --> machine receiver identifier name
 * %7% --> message $timestamp
 */
static std::string formatLifelineId(
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
						aLifeline.getParent().getNameID() : "")
				% aLifeline.getNameID()
				<< std::flush;

		return( oss.str() );
	}
	else
	{
		return( RuntimeLib::RID_ENVIRONMENT.getNameID() );
	}
}

void BasicTraceFormatter::formatIO(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );
//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	ossValue.str("");
	ossValue.setSymbexValueCSS( os );

	aTracePoint.formatValueStream( ossValue );

	const InstanceOfPort & aPort = aTracePoint.object->to< InstanceOfPort >();
	RuntimeID ridContainer = aTracePoint.RID.getCommunicator( aPort );

	std::string sender;
	std::string receiver;
	std::string timestamp = "$timestamp";

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

		if( aTracePoint.config.hasTimestamp() )
		{
			timestamp = aTracePoint.config.getTimestamp().str();
		}
	}

	os << formatter
//			% aTracePoint.RID.strPid()
			% ridContainer.strPid()

//			% aTracePoint.machine->getNameID()
			% ridContainer.getInstance()->getNameID()
//			% aTracePoint.RID.getFullyQualifiedNameID()

			% aTracePoint.object->getNameID()
			% ossValue.str()
			% sender
			% receiver
			% timestamp;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << " ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


void BasicTraceFormatter::formatBuffer(OutStream & os,
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
			% aTracePoint.machine->getNameID()
			% aTracePoint.object->getNameID()
			% oss.str();

	os << END_WRAP;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << " ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}


void BasicTraceFormatter::wrap_format(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.machine )
			<< "TracePoint::machine !!!"
			<< SEND_EXIT;
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aTracePoint.object )
			<< "TracePoint::object !!!"
			<< SEND_EXIT;

	OSS oss( AVM_STR_INDENT , os );
	aTracePoint.formatValueStream( oss << IGNORE_FIRST_TAB );

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getNameID()
			% aTracePoint.object->getNameID()
			% oss.str();

	os << END_WRAP;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << " ==> " << AVM_SPC_INDENT;
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
void BasicTraceFormatter::dotFormatCondition(OutStream & os,
		const std::string & formatPattern, const BF & aCode)
{
	boost::format formatter(formatPattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter % aCode.str();

	os << END_WRAP;
}

/**
 * EXECUTION INFORMATION
 * Info: ID = value
 */

void BasicTraceFormatter::formatExecutionInformation(OutStream & os,
		const TracePoint & aTracePoint, const std::string & pattern)
{
	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter % aTracePoint.value.str();

	os << END_WRAP;
}


/**
 * META ELEMENT
 * @trace{ ... }
 * @debug{ ... }
 * @informal{ ... }
* %1% --> machine runtime pid
* %2% --> machine container identifier
* %3% --> object identifier
* %4% --> value as operand toString
*/
void BasicTraceFormatter::formatMetaElement(OutStream & os,
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
	ossValue.setSymbexValueCSS( os );

	aTracePoint.formatValueStream( ossValue );

	String::ENABLE_QUOTE_PRINTING = saveFlag;

	std::string strValue = ossValue.str();
	StringTools::replaceAllEscapeSequences(strValue);

	boost::format formatter(pattern);
	formatter.exceptions( boost::io::no_error_bits );

	os << mWrapData << formatter
			% (aTracePoint.RID.valid() ? aTracePoint.RID.strPid() : "<pid#?>")
			% aTracePoint.machine->getNameID()
			% aTracePoint.object->getNameID()
			% strValue;

	os << END_WRAP;

AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,
		aTracePoint.EC.isnotNullref() )

	os << " ==> " << AVM_SPC_INDENT;
	aTracePoint.EC.traceMinimum(os);
	os << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE )

	os << std::flush;
}



} /* namespace sep */
