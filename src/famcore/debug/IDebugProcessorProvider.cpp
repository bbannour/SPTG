/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "IDebugProcessorProvider.h"

#include <fml/common/ObjectElement.h>

#include <fml/executable/ExecutableQuery.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeForm.h>

#include <fml/template/TimedMachine.h>

#include <fml/trace/TraceFactory.h>
#include <fml/trace/TracePoint.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include  <famcore/queue/ExecutionQueue.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/SymbexEngine.h>

#include <util/avm_vfs.h>


namespace sep
{


/**
 * DESTRUCTOR
 */
IDebugProcessorProvider::~IDebugProcessorProvider()
{
	delete( mDebugTraceFactory );
}


/*
prototype processor::debugger "debugger" as avm::processor.DEBUGGER is
// Enable or not debuging in Diversity processes
section DEBUG#SCHEDULING
	@filter#detail = true;
	@filter#initialize = true;

	@prefilter = true;
	@prefilter#detail = true;
	@prefilter#finalize = true;

	@postfilter = true;
	@postfilter#detail = true;
	@postfilter#finalize = true;

	@preprocess = true;
	@preprocess#detail= true;

	@postprocess = true;
	@postprocess#detail = true;
endsection DEBUG#SCHEDULING

section DEBUG#PROPERTY
	// Absolute or relative (from LOCATION@log folder) script file path
	@script = "path/to/file/diversity.dbg";

	// Enable Debug Command Shell REPL
	@shell = true;
endsection DEBUG#PROPERTY

section DEBUG#BREAKPOINT
	// The step of first break
	@step    = 100;

	// Break on this context ID number before his execution
	@context = 21;

	// The periodic break base on step count and the first break step
	@period  = 10;
endsection DEBUG#BREAKPOINT

section DEBUG#TRACE
	@var = var#id;
	@var = "machine#id->var#id";

	@buffer = buffer#id;
	@buffer = "machine#id->buffer#id";

	@port = port#id;
	@port = "machine#id->port#id;

	@signal = signal#id;
	@signal = "machine#id->signal#id";

	@machine = machine#id;
	@machine = "machine#id->machine#id";

	@state = state#id;
	@state = "machine#id->state#id";
endsection DEBUG#TRACE
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugConfigureImpl(
		const WObject * wfParameterObject)
{
	////////////////////////////////////////////////////////////////////////////
	// DEBUG#PROPERTY
	const WObject * thePROPERTY =
			Query::getRegexWSequenceOrElse(wfParameterObject,
					OR_WID2(SUFFIX_WID("debug", "ger"), "DEBUG"),
					PREFIX_WID("DEBUG", "PROPERTY"));

	mDebugScriptFile = Query::getWPropertyString(thePROPERTY, "script", "");

	if( not mDebugScriptFile.empty() )
	{
		mDebugScriptFile = VFS::native_path(
				mDebugScriptFile, VFS::ProjectLogPath );
	}

	mDebugConsoleFlag = Query::getWPropertyBoolean(thePROPERTY, "shell", true);


	////////////////////////////////////////////////////////////////////////////
	// DEBUG#SCHEDULING
	const WObject * theSCHEDULING = Query::getRegexWSequence(wfParameterObject,
			OR_WID2( CONS_WID2("debug", "(scheduling|enabling)"),
			CONS_WID2("DEBUG", "SCHEDULING")), thePROPERTY);

	mDebugFilteringDetailFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("filter", "detail"), false);

	mDebugFilteringInitializeFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("filter", "initialize"), false);


	mDebugPrefilteringFlag = Query::getWPropertyBoolean(
			theSCHEDULING, "prefilter", false);

	mDebugPrefilteringDetailFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("prefilter", "detail"),
			mDebugFilteringDetailFlag);

	mDebugPreFilteringInitializeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("prefilter", "initialize"), false)
			|| mDebugPrefilteringDetailFlag;

	mDebugPrefilteringFlag = mDebugPreFilteringInitializeFlag;


	mDebugPrefilteringFinalizeFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("prefilter", "finalize"), false);


	mDebugPostfilteringFlag = Query::getWPropertyBoolean(
			theSCHEDULING, "postfilter", false);

	mDebugPostfilteringDetailFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("postfilter", "detail"),
			mDebugFilteringDetailFlag);

	mDebugPostFilteringInitializeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("postfilter", "initialize"), false)
			|| mDebugPostfilteringFlag;

	mDebugPostfilteringFlag = mDebugPostFilteringInitializeFlag;

	mDebugPostfilteringFinalizeFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("postfilter", "finalize"), false);


	mDebugPreprocessingFlag = Query::getWPropertyBoolean(
			theSCHEDULING, "preprocess", false);

	mDebugPreprocessingDetailFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("preprocess", "detail"), false);


	mDebugPreprocessingInitializeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("preprocess", "initialize"), false)
			|| mDebugPreprocessingFlag;

	mDebugPreprocessingFinalizeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("preprocess", "finalize"), false)
			|| mDebugPreprocessingFlag;

	mDebugPreprocessingFlag = mDebugPreprocessingInitializeFlag
							|| mDebugPreprocessingFinalizeFlag;


	mDebugPostprocessingFlag = Query::getWPropertyBoolean(
			theSCHEDULING, "postprocess", false);

	mDebugPostprocessingDetailFlag = Query::getRegexWPropertyBoolean(
			theSCHEDULING, CONS_WID2("postprocess", "detail"), false);


	mDebugPostprocessingInitializeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("postprocess", "initialize"), false)
			|| mDebugPostprocessingFlag;

	mDebugPostprocessingFinalizeFlag = Query::getRegexWPropertyBoolean(
				theSCHEDULING, CONS_WID2("postprocess", "finalize"), false)
			|| mDebugPostprocessingFlag;

	mDebugPostprocessingFlag = mDebugPostprocessingInitializeFlag
							|| mDebugPostprocessingFinalizeFlag;


	////////////////////////////////////////////////////////////////////////////
	// DEBUG#BREAKPOINT
	const WObject * theBREAKPOINT = Query::getRegexWSequence(
			wfParameterObject, CONS_WID2("(DEBUG", ")?BREAKPOINT"), thePROPERTY);

	mDebugBreakpointEvalStep = std::max( static_cast< avm_integer_t>( 1 ),
			Query::getWPropertyInteger(theBREAKPOINT, "step", 1) );

	mDebugBreakpointEvalContext = std::max( static_cast< avm_integer_t>( 0 ),
			Query::getWPropertyInteger(theBREAKPOINT, "context", 0) );

	mDebugBreakpointEvalStepPeriod = std::max( static_cast< avm_integer_t>( 1 ),
			Query::getWPropertyInteger(theBREAKPOINT, "period", 1) );


	////////////////////////////////////////////////////////////////////////////
	// Trace Factory tools
	if( TimedMachine::SYSTEM_VAR_DELTA_TIME != nullptr )
	{
		ExecutableQuery XQuery( mDebugConfiguration );

		mDebugDeltaTimeVariable = XQuery.getVariableByAstElement(
			(* TimedMachine::SYSTEM_VAR_DELTA_TIME)).to_ptr< InstanceOfData >();
	}

	mDebugTraceFactory = new TraceFactory(mDebugConfiguration,
			mDebugProcessor->getENV(), wfParameterObject,
			ExecutableForm::nullref(), mDebugDeltaTimeVariable);

	const ExecutionData & theMainED =
			mDebugProcessor->getConfiguration().getMainExecutionData();

	mDebugParametersMachine.RID     = theMainED.getParametersRID();
	mDebugParametersMachine.machine = mDebugParametersMachine.RID.getInstance();
	mDebugParametersMachine.object  = mDebugParametersMachine.machine;


	////////////////////////////////////////////////////////////////////////////
	// DEBUG#TRACE
	const WObject * theTRACE = Query::getWSequenceOrElse(
			wfParameterObject, "DEBUG#TRACE", "DEBUG");
	if( (theTRACE != WObject::_NULL_)
		&& theTRACE->hasOwnedElement()
		&& mDebugTraceFactory->configure(
				theTRACE, mDebugTraceSequence, (& theMainED)) )
	{
		for( const auto & itPoint : mDebugTraceSequence.points )
		{
			if( itPoint.is< TracePoint >() )
			{
				dbgTracePoint = itPoint.to_ptr< TracePoint >();

				switch( dbgTracePoint->nature )
				{
					case ENUM_TRACE_POINT::TRACE_COM_NATURE:
					case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
					case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
					case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
					case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
					{
						mDebugSelectedPorts.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
					{
						mDebugSelectedTimeVar = dbgTracePoint;
						break;
					}
					case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
					{
						mDebugSelectedVariables.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_BUFFER_NATURE:
					{
						mDebugSelectedBuffers.append( dbgTracePoint );
						break;
					}

					case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
					{
						mDebugSelectedMachines.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
					{
						mDebugSelectedStatemachines.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
					{
						mDebugSelectedStates.append( dbgTracePoint );
						break;
					}

					case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
					{
						mDebugSelectedTransitions.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:
					{
						mDebugSelectedRoutines.append( dbgTracePoint );
						break;
					}
					case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:
					{
						mDebugSelectedRunnables.append( dbgTracePoint );
						break;
					}

					default:
					{
						break;
					}
				}
			}
		}

		if( mDebugSelectedVariables.nonempty() )
		{
			mDebugSelectedVariable = mDebugSelectedVariables.first();
		}

		if( mDebugSelectedPorts.nonempty() )
		{
			mDebugSelectedPort = mDebugSelectedPorts.first();
		}

		if( mDebugSelectedBuffers.nonempty() )
		{
			mDebugSelectedBuffer = mDebugSelectedBuffers.first();
		}

		if( mDebugSelectedMachines.nonempty() )
		{
			mDebugSelectedMachine = mDebugSelectedMachines.first();
		}

		if( mDebugSelectedStates.nonempty() )
		{
			mDebugSelectedState = mDebugSelectedStates.first();
		}

		if( mDebugSelectedStatemachines.nonempty() )
		{
			mDebugSelectedStatemachine = mDebugSelectedStatemachines.first();
		}

		if( mDebugSelectedTransitions.nonempty() )
		{
			mDebugSelectedTransition = mDebugSelectedTransitions.first();
		}

		if( mDebugSelectedRoutines.nonempty() )
		{
			mDebugSelectedRoutine = mDebugSelectedRoutines.first();
		}

		if( mDebugSelectedRunnables.nonempty() )
		{
			mDebugSelectedRunnable = mDebugSelectedRunnables.first();
		}
	}

	////////////////////////////////////////////////////////////////////////////
	// Other Property
	mDebugEvalStepCount = 0;

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// PRE-PROCESSING API
////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugPreprocessing()
{
	dbgQueue = &( mDebugProcessor->getExecutionQueue().getInitQueue() );

	if( dbgQueue->nonempty() )
	{
		mDebugSelectedContext = dbgQueue->first();
	}

	debugReadEvalCommand();

	if( mDebugPreprocessingDetailFlag )
	{
		for( const auto & itEC : *dbgQueue )
		{
			debugPreprocessing( itEC );
		}
	}

	return( true );
}

bool IDebugProcessorProvider::debugPreprocessing(const ExecutionContext * anEC)
{
	mDebugSelectedContext = anEC;

	mDebugPromptPrefix = "PRE-PROCESSING-DETAIL";

	debugReadEvalCommand();

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// POST-PROCESSING API
////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugPostprocessing()
{
	mDebugSelectedContext = nullptr;

	debugReadEvalCommand();

	if( mDebugPostprocessingDetailFlag
		&& mDebugProcessor->getConfiguration().hasExecutionTrace() )
	{
		dbgLeafEC.clear();
		mDebugProcessor->computeLeafEC(
				mDebugProcessor->getConfiguration().getExecutionTrace(),
				dbgLeafEC);

		dbgQueue = & dbgLeafEC;

		//!! Detail on what ? leaf EC ?
		for( const auto & itEC : *dbgQueue )
		{
			debugPostprocessing( itEC );
		}
	}

	return( true );
}

bool IDebugProcessorProvider::debugPostprocessing(const ExecutionContext * anEC)
{
	mDebugSelectedContext = anEC;

	mDebugPromptPrefix = "POST-PROCESSING-DETAIL";

	debugReadEvalCommand();

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// ACTIVATOR TRIGGER TOOLS
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugActivatorTriggering()
{
	dbgQueue = &( mDebugProcessor->getExecutionQueue().getReadyQueue() );

	if( dbgQueue->nonempty() )
	{
		if( (++mDebugEvalStepCount >= mDebugBreakpointEvalStep) )
		{
			mDebugEnabledFlag = true;

			mDebugBreakpointEvalStep =
					mDebugEvalStepCount + mDebugBreakpointEvalStepPeriod;

			if( dbgQueue->nonempty() )
			{
				mDebugSelectedContext = dbgQueue->first();
			}
		}
		else
		{
			mDebugEnabledFlag = false;
		}

		if( mDebugBreakpointEvalContext > 0 )
		{
			for( const auto & itEC : *dbgQueue )
			{
				if( itEC->getIdNumber() == mDebugBreakpointEvalContext )
				{
					mDebugEnabledFlag = true;

					mDebugSelectedContext = itEC;

					mDebugBreakpointEvalContext = 0;

					AVM_OS_COUT << std::endl << "Breakpoint Context reached :> ";
					mDebugSelectedContext->traceMinimum( AVM_OS_COUT );
				}
			}
		}
	}
	else
	{
		mDebugEnabledFlag = false;
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// INITIALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugFilteringInitialize()
{
	dbgQueue = &( mDebugProcessor->getExecutionQueue().getInitQueue() );

	if( dbgQueue->nonempty() )
	{
		mDebugSelectedContext = dbgQueue->first();
	}

	mDebugPromptPrefix = "FILTERING-INITIALIZE";

	debugReadEvalCommand();

	if( mDebugFilteringDetailFlag )
	{
		for( const auto & itEC : *dbgQueue )
		{
			debugFilteringInitialize( itEC );
		}
	}

	return( true );
}

bool IDebugProcessorProvider::debugFilteringInitialize(const ExecutionContext * anEC)
{
	mDebugSelectedContext = anEC;

	mDebugPromptPrefix = "FILTERING-INITIALIZE-DETAIL";

	debugReadEvalCommand();

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FINALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugFilteringFinalize()
{
	dbgQueue = &( mDebugProcessor->getExecutionQueue().getInitQueue() );

	if( mDebugPrefilteringFlag )
	{
		if( dbgQueue->nonempty() )
		{
			mDebugSelectedContext = dbgQueue->first();
		}

		mDebugPromptPrefix = "FILTERING-FINALIZE";

		debugReadEvalCommand();

		if( mDebugFilteringDetailFlag )
		{
			for( const auto & itEC : *dbgQueue )
			{
				debugFilteringFinalize( itEC );
			}
		}
	}

	return( true );
}

bool IDebugProcessorProvider::debugFilteringFinalize(const ExecutionContext * anEC)
{
	mDebugSelectedContext = anEC;

	mDebugPromptPrefix = "FILTERING-FINALIZE-DETAIL";

	debugReadEvalCommand();

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugPrefiltering()
{
	debugActivatorTriggering();

	if( mDebugEnabledFlag )
	{
		dbgQueue = &( mDebugProcessor->getExecutionQueue().getReadyQueue() );

		if( dbgQueue->nonempty() )
		{
			mDebugSelectedContext = dbgQueue->first();
		}

		mDebugPromptPrefix = "PRE-FILTERING";

		debugReadEvalCommand();

		if( mDebugPrefilteringDetailFlag )
		{
			for( const auto & itEC : *dbgQueue )
			{
				debugPrefiltering( itEC );
			}
		}
	}

	return( true );
}

bool IDebugProcessorProvider::debugPrefiltering(const ExecutionContext * anEC)
{
	if( mDebugEnabledFlag )
	{
		mDebugSelectedContext = anEC;

		mDebugPromptPrefix = "PRE-FILTERING-DETAIL";

		debugReadEvalCommand();
	}

	return( true );
}


bool IDebugProcessorProvider::debugPrefilteringFinalize()
{
	if( mDebugEnabledFlag )
	{
		dbgQueue = &( mDebugProcessor->getExecutionQueue().getReadyQueue() );

		if( dbgQueue->nonempty() )
		{
			mDebugSelectedContext = dbgQueue->first();
		}

		mDebugPromptPrefix = "PRE-FILTERING-FINALIZE";

		debugReadEvalCommand();
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool IDebugProcessorProvider::debugPostfiltering()
{
	if( mDebugEnabledFlag )
	{
		dbgQueue = &( mDebugProcessor->getExecutionQueue().getResultQueue() );

		if( mDebugEnabledFlag )
		{
			if( dbgQueue->nonempty() )
			{
				mDebugSelectedContext = dbgQueue->first();
			}

			mDebugPromptPrefix = "POST-FILTERING";

			debugReadEvalCommand();

			if( mDebugPostfilteringDetailFlag )
			{
				for( const auto & itEC : *dbgQueue )
				{
					debugPostfiltering( itEC );
				}
			}
		}
	}

	return( mDebugProcessor->getExecutionQueue().hasResult() );
}


bool IDebugProcessorProvider::debugPostfiltering(const ExecutionContext * anEC)
{
	if( mDebugEnabledFlag )
	{
		mDebugSelectedContext = anEC;

		mDebugPromptPrefix = "POST-FILTERING-DETAIL";

		debugReadEvalCommand();
	}

	return( true );
}


bool IDebugProcessorProvider::debugPostfilteringFinalize()
{
	if( mDebugEnabledFlag )
	{
		dbgQueue = &( mDebugProcessor->getExecutionQueue().getResultQueue() );

		if( dbgQueue->nonempty() )
		{
			mDebugSelectedContext = dbgQueue->first();
		}

		mDebugPromptPrefix = "POST-FILTERING-FINALIZE";

		debugReadEvalCommand();
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// SCRIPT PROCESSING
////////////////////////////////////////////////////////////////////////////////

void IDebugProcessorProvider::debugReadEvalCommand()
{
	if( not mDebugScriptFile.empty() )
	{
		debugReadEvalScript();
	}

	if( mDebugConsoleFlag )
	{
		if( mDebugScriptFile.empty() )
		{
			AVM_OS_COUT << std::endl;
		}

		debugReadEvalCommandLoop();
	}
}


void IDebugProcessorProvider::debugReadEvalScript()
{
	std::ifstream aScriptStream( mDebugScriptFile );

	if( isDebugScript(aScriptStream) )
	{
		debugReadEvalScript(aScriptStream);
	}

	aScriptStream.close();
}

bool IDebugProcessorProvider::isDebugScript(std::ifstream & aScriptStream)
{
	if( aScriptStream.good() )
	{
		std::getline(aScriptStream, dbgCommandLine);

		StringTools::ltrim( dbgCommandLine );

		if( (dbgCommandLine.find("#!diversity") == 0) ||
			(dbgCommandLine.find("#!symbex") == 0)    ||
			(dbgCommandLine.find("#!avm") == 0) )
		{
			return( aScriptStream.good() );
		}
	}

	return( false );
}

void IDebugProcessorProvider::debugReadEvalScript(std::ifstream & aScriptStream)
{
	while( aScriptStream.good() )
	{
		std::getline(aScriptStream, dbgCommandLine);
		StringTools::ltrim( dbgCommandLine );

		if( dbgCommandLine.empty() )
		{
			//!! IGNORE SPACE --> continue
		}
		else
		{
			debugEvalCommand();
		}
	}
}


void IDebugProcessorProvider::debugReadEvalCommandLoop()
{
	dbgContinueREPL = true;

	AVM_OS_COUT << std::flush << "Enter a command [or help] ";

	while( dbgContinueREPL )
	{
		AVM_OS_COUT << mDebugPromptPrefix
				<< " { step: " << mDebugEvalStepCount
				<< " ( + " << mDebugBreakpointEvalStepPeriod
				<< " )==> break: " << mDebugBreakpointEvalStep;
		if( mDebugBreakpointEvalContext > 0 )
		{
			AVM_OS_COUT << " | ctx: " << mDebugBreakpointEvalContext;

		}
		AVM_OS_COUT << " } [ " << std::flush;

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << ( mDebugTraceFullPathFlag ? "path" : "ctx" )
					<< ":" << mDebugSelectedContext->getIdNumber();
		}
		if( dbgDetailsMin || dbgDetailsMed || dbgDetailsMax )
		{
			AVM_OS_COUT << " , detail:";
			if( dbgDetailsMax ) { AVM_OS_COUT << "*"; }
			if( dbgDetailsMed ) { AVM_OS_COUT << "+"; }
			if( dbgDetailsMin ) { AVM_OS_COUT << "-"; }
			AVM_OS_COUT << " ";
		}
		AVM_OS_COUT << " ] :> " << std::endl;

		if( not dbgCommandLine.empty() )
		{
			dbgCommandLineHistory.rremove( dbgCommandLine );
			dbgCommandLineHistory.push_back( dbgCommandLine );
		}

		std::getline(std::cin, dbgCommandLine);
		StringTools::ltrim( dbgCommandLine );

		if( dbgCommandLine.empty() )
		{
			//!! IGNORE SPACE -->continue
		}
		else
		{
			if( dbgCommandLine[0] == '!' )
			{
				debugReadHistoryCommand();
			}

			debugEvalCommand();
		}
	}
}


void IDebugProcessorProvider::debugReadHistoryCommand()
{
	dbgOffset = AVM_NUMERIC_MAX_SIZE_T;

	if( dbgCommandLine == "!!" )
	{
		dbgOffset = 0;
	}
	else if( dbgCommandLine.size() > 1 )
	{
		StringTools::ltrim( dbgCommandArg = dbgCommandLine , 1 );

		if( ::isdigit( dbgCommandArg[0] ) )
		{
			from_string<std::size_t>(dbgCommandArg, dbgOffset);
		}
		else
		{
			VectorOfString::const_reverse_iterator cmdIt =
					dbgCommandLineHistory.rbegin();
			VectorOfString::const_reverse_iterator cmdItEnd =
					dbgCommandLineHistory.rend();
			for( dbgOffset = 0; cmdIt != cmdItEnd ; ++cmdIt, ++dbgOffset )
			{
				if( ((*cmdIt)[0] == dbgCommandArg[0]) &&
					(*cmdIt).starts_with(dbgCommandArg) )
				{
					break;
				}
			}
		}
	}

	if( dbgOffset < dbgCommandLineHistory.size() )
	{
		dbgCommandLine = dbgCommandLineHistory.reverse_at(dbgOffset);

		AVM_OS_COUT << "history[" << dbgOffset << "] :> "
				<< dbgCommandLine << std::endl;
	}
}


void IDebugProcessorProvider::debugEvalCommand()
{
	dbgDecodeCommandOk = false;

	// First, try to eval specific processor command for local debugging reason
	if( debugEvalCommandImpl() )
	{
		//!! NOTHING
	}

	else if( (dbgCommandLine[0] == '#') || ( (dbgCommandLine.size() >= 2) &&
			(dbgCommandLine[0] == '/') && (dbgCommandLine[1] == '/') ) )
	{
		//!! IGNORE SINGLE LINE COMMENT -->continue
	}

	else if( dbgDecodeCommand("help", '?' , 'h') )
	{
		dbgCommandHelp();
	}


	else if( dbgDecodeCommand("echo") )
	{
		dbgCommandEcho();
	}

	else if( dbgDecodeCommand("print") )
	{
		dbgCommandPrint();
	}

	else if( dbgDecodeCommand("show") )
	{
		dbgCommandShow();
	}


	else if( dbgDecodeCommand("breakpoint", "bp") )
	{
		AVM_OS_COUT << "The step count     : "
				<< mDebugEvalStepCount << std::endl;

		AVM_OS_COUT << "Interaction period : "
				<< mDebugBreakpointEvalStepPeriod << std::endl;


		AVM_OS_COUT << "Next step interaction breakpoint    : "
				<< mDebugBreakpointEvalStep << std::endl;

		AVM_OS_COUT << "Next context interaction breakpoint : "
				<< mDebugBreakpointEvalContext << std::endl;
	}


	else if( dbgDecodeCommand("config", "cfg") )
	{
		dbgCommandConfig();
	}

	else if( dbgDecodeCommand("scheduler", "sched") )
	{
		AVM_OS_COUT << "Diversity process Scheduler:" << std::endl;

		mDebugProcessor->getControllerUnitManager().toStream( AVM_OS_COUT );
	}


	else if( dbgDecodeCommand("report", "rp") )
	{
		mDebugProcessor->getControllerUnitManager().report(AVM_OS_COUT);

		mDebugProcessor->getSymbexEngine().reportTimeElapsing(AVM_OS_COUT);
	}

	else if( dbgDecodeCommand("save") )
	{
		mDebugProcessor->getConfiguration().serializeComputingResult();
		AVM_OS_COUT << "DONE !!!" << std::endl << std::endl;
	}


	else if( dbgDecodeCommand("shell") )
	{
		if( not mDebugConsoleFlag )
		{
			mDebugConsoleFlag = true;

			AVM_OS_COUT << std::endl;

			mDebugPromptPrefix = "USER";

			debugReadEvalCommandLoop();

			mDebugConsoleFlag = false;
		}
	}


	else if( dbgDecodeCommand("continue") )
	{
		dbgContinueREPL = false;
	}


	else if( dbgDecodeCommand("next", '+') )
	{
		dbgContinueREPL = false;

		dbgCommandNext();
	}


	else if( dbgDecodeCommand("break") )
	{
		dbgContinueREPL = false;

		dbgCommandBreak();
	}


	else if( dbgDecodeCommand("period") )
	{
		dbgCommandPeriod();
	}


	else if( dbgDecodeCommand("queue") )
	{
		dbgCommandQueue();
	}

	else if( dbgDecodeCommand("ec", "ctx") )
	{
		dbgCommandContext();
	}

	else if( dbgDecodeCommand("leaves", "leaf") )
	{
		dbgCommandLeavesContexts();
	}

	else if( dbgDecodeCommand("path") )
	{
		dbgCommandPath();
	}


	else if( dbgDecodeCommand("trace") )
	{
		dbgCommandTrace();
	}

	else if( isDebugStringCommand("detail") )
	{
		dbgCommandTraceDetailLevel();
	}

	else if( dbgDecodeCommand("fullpath") )
	{
		mDebugTraceFullPathFlag = not mDebugTraceFullPathFlag;
	}


	else if( dbgDecodeCommand("vars") )
	{
		dbgCommandVars();
	}
	else if( dbgDecodeCommand("var") )
	{
		dbgCommandVar();
	}
	else if( dbgDecodeCommand("time") )
	{
		dbgCommandTime();
	}



	else if( dbgDecodeCommand("coms") )
	{
		dbgCommandPorts(ENUM_TRACE_POINT::TRACE_COM_NATURE);
	}
	else if( dbgDecodeCommand("ports") )
	{
		dbgCommandPorts(ENUM_TRACE_POINT::TRACE_PORT_NATURE);
	}
	else if( dbgDecodeCommand("messages") )
	{
		dbgCommandPorts(ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE);
	}
	else if( dbgDecodeCommand("signals") )
	{
		dbgCommandPorts(ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE);
	}


	else if( dbgDecodeCommand("com") )
	{
		dbgCommandPort(ENUM_TRACE_POINT::TRACE_COM_NATURE);
	}
	else if( dbgDecodeCommand("port") )
	{
		dbgCommandPort(ENUM_TRACE_POINT::TRACE_PORT_NATURE);
	}
	else if( dbgDecodeCommand("message") )
	{
		dbgCommandPort(ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE);
	}
	else if( dbgDecodeCommand("signal") )
	{
		dbgCommandPort(ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE);
	}



	else if( dbgDecodeCommand("buffers") )
	{
		dbgCommandBuffers();
	}
	else if( dbgDecodeCommand("buffer") )
	{
		dbgCommandBuffer();
	}


	else if( dbgDecodeCommand("machines") )
	{
		dbgCommandMachines();
	}
	else if( dbgDecodeCommand("machine") )
	{
		dbgCommandMachine();
	}

	else if( dbgDecodeCommand("parameters", "parameter", "params", "param") )
	{
		dbgCommandParametersMachine();
	}


	else if( dbgDecodeCommand("states") )
	{
		dbgCommandStates();
	}
	else if( dbgDecodeCommand("state") )
	{
		dbgCommandState();
	}


	else if( dbgDecodeCommand("transitions", "transs") )
	{
		dbgCommandTransitions();
	}
	else if( dbgDecodeCommand("transition", "trans") )
	{
		dbgCommandTransition();
	}

	else if( dbgDecodeCommand("routines") )
	{
		dbgCommandRoutines();
	}
	else if( dbgDecodeCommand("routine") )
	{
		dbgCommandRoutine();
	}


	else if( dbgDecodeCommand("enable") )
	{
		dbgCommandEnableDisableProcess( true );
	}


	else if( dbgDecodeCommand("disable") )
	{
		dbgCommandEnableDisableProcess( false );
	}


	else if( dbgDecodeCommand("verbosity", "verbose") )
	{
		dbgCommandVerbosityLevel();
	}


	else if( dbgDecodeCommand("debug#level") )
	{
		dbgCommandDebugLevel();
	}


	else if( dbgDecodeCommand("debug#flag") )
	{
		dbgCommandDebugFlag( true );
	}


	else if( dbgDecodeCommand("debug#flag#off") )
	{
		dbgCommandDebugFlag( false );
	}


	else if( dbgDecodeCommand("bye", "stop") )
	{
		dbgContinueREPL = false;
	}
	else if( dbgDecodeCommand("stop") )
	{
		dbgContinueREPL = false;
	}

	else if( dbgDecodeCommand("exit", "quit") )
	{
		dbgContinueREPL = false;

		mDebugProcessor->
		getSymbexRequestManager().postRequestStop( mDebugProcessor );
	}

	else if( dbgDecodeCommand("history", "hty") )
	{
		dbgCommandHistory();
	}

	else
	{
		AVM_OS_COUT << "<Unknown Command>: " << dbgCommandLine
				<< std::endl << std::endl;
//		AVM_OS_COUT << DEBUG_SHELL_COMMAND_SUMMARY << std::endl;

		dbgCommandLine = "";
	}
}


void IDebugProcessorProvider::dbgCheckCommandDetailsArg()
{
	if( not dbgCommandArg.empty() )
	{
		if( dbgCommandArg[0] == '-' )
		{
			dbgDetailsMin = true;

			StringTools::ltrim( dbgCommandArg , 1 );
		}

		if( dbgCommandArg[0] == '+' )
		{
			dbgDetailsMed = true;

			StringTools::ltrim( dbgCommandArg , 1 );
		}

		if( dbgCommandArg[0] == '*' )
		{
			dbgDetailsMax = true;

			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}
}


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_SUMMARY =
		"List of classes of commands :\n"
		"\t?    -- \n"
		"\th    -- \n"
		"\thelp -- Print this help\n\n"

		"\thistory    -- help on command for invoking an old command\n"

		"\tcontrol    -- help on command for controlling the debug process\n"

		"\tqueue      -- help on command for analyzing the execution queue\n"

		"\tctx        -- help on command for execution context selection\n"

		"\tdata       -- help on command for analyzing the execution data\n\n"

		"\tprint      -- help on command for printing in the console: text message, ...\n"

		"\treport     -- help on command for reporting on a snapshot of the evaluation\n"

		"\tbreakpoint -- help on command for setting step parameters\n"

		"\toption     -- help on command for enable specific debug process\n"

		"\tlog        -- help on command for enable debug level or flag\n\n"

		"Type \"help\" followed by a class name for a list of commands in that class.\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_HISTORY =
		"\thistory  -- Print the command history list\n"
		"\t!!       -- Re-eval the last command\n"
		"\t!N       -- Re-eval the last N-th command\n"
		"\t!prefix  -- Re-eval the first of last command which starts with 'prefix'\n";



std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_CONTROL =
		"\tbye      -- \n"
		"\tstop     -- \n"
		"\t+        -- \n"
		"\tcontinue -- Stop the the interaction process, "
						"continue Diversity processing\n\n"

		"\tquit     -- Quit the Diversity process\n"
		"\texit     -- Exit the Diversity process\n\n"

		"\tbreak    -- Continue until the next break for a given Context Number\n"
		"\t\tbreak?  : Waiting for the user gives a Context Number\n"
		"\t\tbreak N : A Context Number N\n"

		"\tnext     -- Continue for a given Number of step until the next interaction\n"
		"\t\tnext?   : Waiting for the user gives a number of step\n"
		"\t\tnexti   : One step\n"
		"\t\tnext N  : A number N of step\n\n"

		"\tperiod   -- Set an interaction period number\n"
		"\t\tperiod?  : Waiting for the user gives an interaction period number\n"
		"\t\tperiod N : An interaction period number\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_QUEUE =
		"\tqueue  -- Print all execution queue\n"
		"\t\tqueue?        : Waiting for the user selects a queue in "
							"{ init , waiting , ready , result , failed }\n"
		"\t\tqueue#init    : the 'init' queue\n"
		"\t\tqueue#waiting : the 'waiting' queue\n"
		"\t\tqueue#ready   : the 'ready' queue\n"
		"\t\tqueue#result  : the 'result' queue\n"
		"\t\tqueue#failed  : the 'failed' queue\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_CONTEX =
		"\tleaves   -- \n"
		"\tleaf     -- Show all executions contexts leaves\n"
		"\tleaf?    :  Waiting for the user to select a runtime tag to select contexts leaves\n"
		"\t         :  among { DEADELOCK EXIT LIMIT ERROR COVERAGE ACHIEVED PASS FAILED ABORT VERDICT ANALYSIS ...}\n"
		"\tleaf tag :  Show all executions contexts leaves w.r.t. a runtime tag\n"
		"\tpath     -- Print current execution path from selected context\n"
		"\tec       -- \n"
		"\tctx      -- Print current execution context\n"
		"\t\tctx?   :  Waiting for the user to select an execution context ID number\n"
		"\t\tctx N  :  Select the given execution context N\n"
		"\t\t\tSearching order: (1) current selection child, (2) ancestors, "
		"(3) all the the execution graph !!!";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_DATA =
		"\tvar      -- Print value from selected Context for a selected variable\n"
		"\t\tvar?   : Waiting for the user gives a variable ID\n"
		"\t\tvar ID : Select the given variable ID\n\n"

		"\tport     -- Print value from selected Context for a selected port\n"
		"\t\tport?   : Waiting for the user gives a port ID\n"
		"\t\tport ID : Select the given port ID\n\n"

		"\tbuffer   -- Print value from selected Context for a selected buffer\n"
		"\t\tbuffer?   : Waiting for the user gives a buffer ID\n"
		"\t\tbuffer ID : Select the given buffer ID\n\n"

		"\tmachine  -- Print selected machine runtime data\n"
		"\t\tmachine?   : Waiting for the user gives a machine ID\n"
		"\t\tmachine ID : Select the given machine ID\n\n"

		"\tstate    -- Print a selected state code\n"
		"\t\tstate?   : Waiting for the user gives a state ID\n"
		"\t\tstate ID : Select the given state ID\n\n"

		"\ttransition -- Print a selected transition code\n"
		"\t\ttransition?   : Waiting for the user gives a transition ID\n"
		"\t\ttransition ID : Select the given transition ID\n\n"

		"\troutine  -- Print a selected routine code\n"
		"\t\troutine?   : Waiting for the user gives a routine ID\n"
		"\t\troutine ID : Select the given routine ID\n"

		"\ttrace    -- Trace of all selected data specified in << section DEBUG#TRACE >>\n"

		"\tdetail   -- Enable/disable detail level: "
		"- for minimum , + for medium , * for maximum , nothing for default\n"

		"\tfullpath -- Enable/disable the << full path trace flag >> for showing "
		"selected data from the selected context to the root !\n";



std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_PRINT =
		"\techo msg -- print the message text in the console'\n"

		"\tprint    -- print ...\n"
		"\tshow     -- shouw ...\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_REPORT =
		"\tcfg      -- \n"
		"\tconfig   -- Print current Diversity processing configuration\n"

		"\tscheduler-- Print current Diversity processing scheduler\n"

		"\trp       -- \n"
		"\treport   -- Print current Diversity processing report\n"

		"\tsave     -- Save a snapshot of the Diversity process\n\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_BREAKPOINT =
		"\tbp\n"
		"\tbreakpoint -- Print breakpoints information:\n"
		"\t\tThe step count and the interaction period for break\n"
		"\t\tThe next step interaction breakpoint\n"
		"\t\tThe next context interaction breakpoint\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_OPTION =
		"\tenable   -- Enable an interaction for a givent process\n"
		"\t\tenable?   : Waiting for the user selects a process in "
							"{ prefilter , postfilter , preprocess , postprocess }\n"
		"\t\tenable#prefilter   : the 'prefilter' process\n"
		"\t\tenable#postfilter  : the 'postfilter' process\n"
		"\t\tenable#preprocess  : the 'preprocess' process\n"
		"\t\tenable#postprocess : the 'postprocess' process\n\n"


		"\tdisable  -- Disable an interaction for a givent process\n"
		"\t\tdisable?  : Waiting for the user selects a process in "
							"{ prefilter , postfilter , preprocess , postprocess }\n"
		"\t\tdisable#prefilter   : the 'prefilter' process\n"
		"\t\tdisable#postfilter  : the 'postfilter' process\n"
		"\t\tdisable#preprocess  : the 'preprocess' process\n"
		"\t\tdisable#postprocess : the 'postprocess' process\n";


std::string IDebugProcessorProvider::DEBUG_SHELL_COMMAND_LOG =
		"\tverbosity       -- Set verbosity at the given level : "
						"SILENT < MINIMUM < MEDIUM < MAXIMUM\n"
		"\t\tverbosity? : Waiting for the user gives a verbosity level\n\n"


		"\tdebug#level     -- Set debug#level at the given level : "
							"ZERO < LOW < MEDIUM < HIGH < ULTRA\n"
		"\t\tdebug#level? : Waiting from user a debug level\n\n"

		"\tdebug#flag      -- Set debug#flag at the given flag\n"
		"\t\tdebug#flag? : Waiting for the user gives a debug flag\n"

		"\tdebug#flag#off  -- Unset the debug#flag for the given flag\n"
		"\t\tdebug#flag#off? : Waiting from user a debug flag to off\n";



void IDebugProcessorProvider::dbgCommandHelp()
{
	if( dbgCommandArg.empty() )
	{
		AVM_OS_COUT << DEBUG_SHELL_COMMAND_SUMMARY << std::endl;
	}
	else
	{
		if( dbgCommandArg == "?" )
		{
			AVM_OS_COUT << "Select a section { control , print , report , "
					"step , queue , ctx , data , option , log } :> ";

			std::getline(std::cin, dbgCommandArg);
			StringTools::ltrim( dbgCommandArg );
		}
		else if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		if( dbgCommandArg.find("history") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for invoking an old command\n"
					<< DEBUG_SHELL_COMMAND_HISTORY << std::endl;
		}
		else if( dbgCommandArg.find("control") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for controlling the debug process\n"
					<< DEBUG_SHELL_COMMAND_CONTROL << std::endl;
		}
		else if( dbgCommandArg.find("queue") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for analyzing the execution queue\n"
					<< DEBUG_SHELL_COMMAND_QUEUE << std::endl;
		}
		else if( dbgCommandArg.find("ctx") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for execution context selection\n"
					<< DEBUG_SHELL_COMMAND_CONTEX << std::endl;
		}
		else if( dbgCommandArg.find("data") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for analyzing the execution data\n"
					<< DEBUG_SHELL_COMMAND_DATA << std::endl;
		}

		else if( dbgCommandArg.find("print") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for printing in the console: "
					"text message, ...\n"
					<< DEBUG_SHELL_COMMAND_PRINT << std::endl;
		}
		else if( (dbgCommandArg.find("report") != std::string::npos) ||
				(dbgCommandArg == "rp") )
		{
			AVM_OS_COUT << "Help on command for reporting on the evaluation snapshot\n"
					<< DEBUG_SHELL_COMMAND_REPORT << std::endl;
		}
		else if( (dbgCommandArg.find("breakpoint") != std::string::npos) ||
				(dbgCommandArg.find("bp") != std::string::npos) )
		{
			AVM_OS_COUT << "Help on command for breakpoints informations\n"
					<< DEBUG_SHELL_COMMAND_BREAKPOINT << std::endl;
		}
		else if( dbgCommandArg.find("option") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for enable specific debug process\n"
					<< DEBUG_SHELL_COMMAND_OPTION << std::endl;
		}
		else if( dbgCommandArg.find("log") != std::string::npos )
		{
			AVM_OS_COUT << "Help on command for enable debug level or flag\n"
					<< DEBUG_SHELL_COMMAND_LOG << std::endl;
		}
		else
		{
			AVM_OS_COUT << DEBUG_SHELL_COMMAND_SUMMARY << std::endl;
		}
	}

	AVM_OS_COUT << std::endl;

}


void IDebugProcessorProvider::dbgCommandHistory()
{
	if( dbgCommandArg.empty() )
	{
		dbgOffset = dbgCommandLineHistory.size();
	}
	else if( dbgCommandArg == "?" )
	{
		AVM_OS_COUT << "Enter an integer as history command count :> ";

		std::cin >> dbgOffset;
	}
	else
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		from_string<std::size_t>(dbgCommandArg, dbgOffset);
	}

	avm_integer_t historyCount =
			std::min(dbgOffset, dbgCommandLineHistory.size()) - 1;

	AVM_OS_COUT << "Command history :> " << std::endl;
	AVM_OS_COUT << "\t" << "0: <this history command> " << dbgCommandLine << std::endl;
	for( dbgOffset = 1 ; historyCount >= 0 ; ++dbgOffset, --historyCount )
	{
		AVM_OS_COUT << "\t" << dbgOffset << ": "
				<< dbgCommandLineHistory[historyCount] << std::endl;
	}
}


void IDebugProcessorProvider::dbgCommandConfig()
{
	mDebugProcessor->getControllerUnitManager().toStream( AVM_OS_COUT );

	AVM_OS_COUT << std::endl;

	AVM_OS_COUT << "The debug< enable > processes are :> "
			<< ( mDebugPrefilteringFlag ?          " prefilter" : "" )
			<< ( mDebugPrefilteringFinalizeFlag ?  " prefilter#finalize" : "" )
			<< ( mDebugPostfilteringFlag ?         " postfilter" : "" )
			<< ( mDebugPostfilteringFinalizeFlag ? " postfilter#finalize" : "" )
			<< ( mDebugPreprocessingFlag ?         " preprocess" : "" )
			<< ( mDebugPostprocessingFlag ?        " postprocess" : "" )
			<< std::endl;

	AVM_OS_COUT << "The step count        : "
			<< mDebugEvalStepCount << std::endl;

	AVM_OS_COUT << "Next interaction step : "
			<< mDebugBreakpointEvalStep << std::endl;

	AVM_OS_COUT << "Interaction period    : "
			<< mDebugBreakpointEvalStepPeriod << std::endl;

	if( mDebugBreakpointEvalContext > 0 )
	{
		AVM_OS_COUT << "Next interaction ctx  : "
				<< mDebugBreakpointEvalContext << std::endl;
	}

	AVM_OS_COUT << std::endl;


	AVM_OS_COUT << "The user trace element :> ";
	mDebugTraceSequence.toStream(AVM_OS_COUT);

	AVM_OS_COUT << "detail :";
	if( dbgDetailsMin || dbgDetailsMed || dbgDetailsMax )
	{
		if( dbgDetailsMin ) { AVM_OS_COUT << " MINIMUM"; }
		if( dbgDetailsMed ) { AVM_OS_COUT << " MEDIUM" ; }
		if( dbgDetailsMax ) { AVM_OS_COUT << " MAXIMUM"; }
	}
	else
	{
		AVM_OS_COUT << " DEFAULT";
	}

	AVM_OS_COUT << std::endl << std::endl;

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "Selected Context :> ";

		mDebugSelectedContext->traceDefaultEval(AVM_OS_COUT);

		AVM_OS_COUT << std::endl;
	}


	AVM_OS_COUT << "Verbosity level   :> " << avm_strExecVerbosityLevel()
			<< std::endl;
	AVM_OS_COUT << "Debug trace level :> " << avm_strDebugLevel()
			<< std::endl;
	AVM_OS_COUT << "Debug trace flag  :> " << avm_strDebugFlag(" | ")
			<< std::endl << std::endl;
}


void IDebugProcessorProvider::dbgCommandBreak()
{
	if( dbgCommandArg.empty() || (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter an integer as step number :> ";

		std::cin >> dbgIntValue;
	}
	else
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		from_string<avm_integer_t>(dbgCommandArg, dbgIntValue);
	}

	mDebugBreakpointEvalContext =
			std::max(static_cast< avm_integer_t>( 0 ), dbgIntValue);
}


void IDebugProcessorProvider::dbgCommandNext()
{
	if( dbgCommandArg.empty() )
	{
		// Continue until next predefined break step !!!
	}
	else if( dbgCommandArg[0] == 'i' )
	{
		mDebugBreakpointEvalStep = mDebugEvalStepCount + 1;
	}
	else
	{
		if( dbgCommandArg == "?" )
		{
			AVM_OS_COUT << "Enter an integer as step number :> ";

			std::cin >> dbgIntValue;
		}
		else
		{
			if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
			{
				StringTools::ltrim( dbgCommandArg , 1 );
			}

			from_string<avm_integer_t>(dbgCommandArg, dbgIntValue);
		}

		mDebugBreakpointEvalStep = mDebugEvalStepCount +
				std::max(static_cast< avm_integer_t>( 1 ), dbgIntValue);
	}
}


void IDebugProcessorProvider::dbgCommandPeriod()
{
	if( dbgCommandArg.empty() || (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter an integer as step interaction period :> ";

		std::cin >> dbgIntValue;
	}
	else
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		from_string<avm_integer_t>(dbgCommandArg, dbgIntValue);
	}

	mDebugBreakpointEvalStepPeriod =
			std::max(static_cast< avm_integer_t>( 1 ), dbgIntValue);

	mDebugBreakpointEvalStep =
			mDebugEvalStepCount + mDebugBreakpointEvalStepPeriod;
}


void IDebugProcessorProvider::dbgCommandQueue()
{
	if( dbgCommandArg.empty() )
	{
		mDebugProcessor->getExecutionQueue().toStream(AVM_OS_COUT);
	}
	else
	{
		if( dbgCommandArg == "?" )
		{
			AVM_OS_COUT << "Select a queue "
					"{ init , waiting , ready , result , failed } :> ";

			std::getline(std::cin, dbgCommandArg);
			StringTools::ltrim( dbgCommandArg );
		}
		else if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		if( dbgCommandArg.find("init") != std::string::npos )
		{
			AVM_OS_COUT << "the INIT QUEUE :> " << std::endl;
			mDebugProcessor->getExecutionQueue().toStream(
					mDebugProcessor->getExecutionQueue().getInitQueue(),
					AVM_OS_COUT);
		}
		if( dbgCommandArg.find("waiting") != std::string::npos )
		{
			mDebugProcessor->getExecutionQueue().toStreamWaiting(AVM_OS_COUT);
		}
		if( dbgCommandArg.find("ready") != std::string::npos )
		{
			AVM_OS_COUT << "the READY QUEUE :> " << std::endl;
			mDebugProcessor->getExecutionQueue().toStream(
					mDebugProcessor->getExecutionQueue().getReadyQueue(),
					AVM_OS_COUT);
		}
		if( dbgCommandArg.find("result") != std::string::npos )
		{
			AVM_OS_COUT << "the RESULT QUEUE :> " << std::endl;
			mDebugProcessor->getExecutionQueue().toStream(
					mDebugProcessor->getExecutionQueue().getResultQueue(),
					AVM_OS_COUT);
		}
		if( dbgCommandArg.find("failed") != std::string::npos )
		{
			AVM_OS_COUT << "the FAILED QUEUE :> " << std::endl;
			mDebugProcessor->getExecutionQueue().toStream(
					mDebugProcessor->getExecutionQueue().getFailedQueue(),
					AVM_OS_COUT);
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandContext()
{
	if( dbgCommandArg.empty() && (mDebugSelectedContext != nullptr) )
	{
		AVM_OS_COUT << "Selected Context :> ";

		mDebugSelectedContext->traceDefaultEval(AVM_OS_COUT);

		if( dbgDetailsMed || dbgDetailsMax )
		{
			mDebugSelectedContext->toDebugFet(AVM_OS_COUT);
		}
		else if( not dbgDetailsMin )
		{
			mDebugSelectedContext->toDebug(AVM_OS_COUT);
		}

		AVM_OS_COUT << std::endl;

		return;
	}


	else if( dbgCommandArg.empty() || (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter an Execution Context ID number :> ";

		std::cin >> dbgIntValue;
	}
	else
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		from_string<avm_integer_t>(dbgCommandArg, dbgIntValue);
	}


	dbgEC = nullptr;

	if( mDebugSelectedContext !=  nullptr )
	{
		// Searching in the childs of theSelectedContext
		dbgEC = searchContext( mDebugSelectedContext,
				std::max(static_cast< avm_integer_t>( 0 ), dbgIntValue) );
		if( dbgEC != nullptr )
		{
			mDebugSelectedContext = dbgEC;
		}

		// If not found, Searching in the ancestors of theSelectedContext
		if( dbgEC == nullptr )
		{
			dbgEC = mDebugSelectedContext;
			for( ; dbgEC != nullptr ; dbgEC = dbgEC->getPrevious() )
			{
				if( dbgEC->getIdNumber() == dbgIntValue )
				{
					mDebugSelectedContext = dbgEC;
					break;
				}
			}
		}
	}

	// If not found, Searching in the current dbgQueue
	if( dbgEC == nullptr )
	{
		if( (dbgQueue != nullptr) && dbgQueue->nonempty() )
		{
			for( const auto & itEC : *dbgQueue )
			{
				if( itEC->getIdNumber() == dbgIntValue )
				{
					mDebugSelectedContext = dbgEC = itEC;
					break;
				}
			}
		}

		// If not found, Searching in the Execution graph from the root context
		if( dbgEC == nullptr )
		{
			for( const auto & itEC :
				mDebugProcessor->getConfiguration().getFirstExecutionTrace() )
			{
				dbgEC = searchContext( itEC,
					std::max(static_cast< avm_integer_t>( 0 ), dbgIntValue) );

				if( dbgEC != nullptr )
				{
					mDebugSelectedContext = dbgEC;
					break;
				}
			}
		}
	}


	if( dbgEC == nullptr )
	{
		AVM_OS_COUT << "Unfound Execution Context by id: " << dbgIntValue
				<< " !!! Unchange current selection ..."
				<< std::endl << std::endl;
	}

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "Selected Context :> ";

		mDebugSelectedContext->traceDefaultEval(AVM_OS_COUT);

		if( dbgDetailsMed || dbgDetailsMax )
		{
			mDebugSelectedContext->toDebugFet(AVM_OS_COUT);
		}
		else if( not dbgDetailsMin )
		{
			mDebugSelectedContext->toDebug(AVM_OS_COUT);
		}

		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgCommandLeavesContexts()
{
	if( dbgCommandArg == "?" )
	{
		AVM_OS_COUT << "Select an Execution Context Tag among" << std::endl
				<< "{ DEADELOCK EXIT LIMIT ERROR COVERAGE ACHIEVED PASS FAILED ABORT VERDICT ANALYSIS ... } :> ";

		std::cin >> dbgCommandArg;
	}

	if( dbgLeafEC.empty() )
	{
		mDebugProcessor->computeLeafEC(
				mDebugProcessor->getConfiguration().getExecutionTrace(),
				dbgLeafEC);
	}

	if( dbgLeafEC.nonempty() )
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		bool isMatch = false;

		for( const auto & itEC : dbgLeafEC )
		{
			if( dbgCommandArg.empty() )
			{
				isMatch = true;
			}
			else
			{
				StringTools::toupper(dbgCommandArg);

				isMatch = hasExecutionContextTag(*itEC, dbgCommandArg);
			}

			if( isMatch )
			{
				itEC->traceMinimum(AVM_OS_COUT);
			}
		}
	}
}

void IDebugProcessorProvider::dbgCommandPath()
{
	if( dbgCommandArg.empty() && (mDebugSelectedContext != nullptr) )
	{
		dbgEC = mDebugSelectedContext;

		AVM_OS_COUT << "Selected Path, current selected context :> " << std::endl;
		dbgEC->traceDefaultEval(AVM_OS_COUT);

		dbgEC->toDebug(AVM_OS_COUT);

		AVM_OS_COUT << std::endl << "Ancestors :> " << std::endl;

		dbgEC = dbgEC->getPrevious();
		for( ; dbgEC != nullptr ; dbgEC = dbgEC->getPrevious() )
		{
			dbgEC->traceDefault(AVM_OS_COUT);

			dbgEC->toDebug(AVM_OS_COUT);
		}

		AVM_OS_COUT << std::endl;

		return;
	}


	else if( dbgCommandArg.empty() || (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter an Execution Context ID number :> ";

		std::cin >> dbgIntValue;
	}
	else
	{
		if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		from_string<avm_integer_t>(dbgCommandArg, dbgIntValue);
	}


	dbgEC = nullptr;

	if( mDebugSelectedContext !=  nullptr )
	{
		// Searching in the childs of mDebugSelectedContext
		dbgEC = searchContext( mDebugSelectedContext,
				std::max(static_cast< avm_integer_t>( 0 ), dbgIntValue) );
		if( dbgEC != nullptr )
		{
			mDebugSelectedContext = dbgEC;
		}

		// If not found, Searching in the ancestors of mDebugSelectedContext
		if( dbgEC == nullptr )
		{
			dbgEC = mDebugSelectedContext;
			for( ; dbgEC != nullptr ; dbgEC = dbgEC->getPrevious() )
			{
				if( dbgEC->getIdNumber() == dbgIntValue )
				{
					mDebugSelectedContext = dbgEC;
					break;
				}
			}
		}
	}

	// If not found, Searching in the current dbgQueue
	if( dbgEC == nullptr )
	{
		if( (dbgQueue != nullptr) && dbgQueue->nonempty() )
		{
			for( const auto & itEC : *dbgQueue )
			{
				if( itEC->getIdNumber() == dbgIntValue )
				{
					mDebugSelectedContext = dbgEC = itEC;
					break;
				}
			}
		}

		// If not found, Searching in the Execution graph from the root context
		if( dbgEC == nullptr )
		{
			for( const auto & itEC :
				mDebugProcessor->getConfiguration().getFirstExecutionTrace() )
			{
				dbgEC = searchContext( itEC,
					std::max(static_cast< avm_integer_t>( 0 ), dbgIntValue) );

				if( dbgEC != nullptr )
				{
					mDebugSelectedContext = dbgEC;
					break;
				}
			}
		}
	}

	if( dbgEC != nullptr )
	{
		AVM_OS_COUT << "Selected Path, current selected context :> " << std::endl;
		dbgEC->traceDefaultEval(AVM_OS_COUT);

		dbgEC->toDebug(AVM_OS_COUT);

		AVM_OS_COUT << std::endl << "Ancestors :> " << std::endl;

		dbgEC = dbgEC->getPrevious();
		for( ; dbgEC != nullptr ; dbgEC = dbgEC->getPrevious() )
		{
			dbgEC->traceDefault(AVM_OS_COUT);

			dbgEC->toDebug(AVM_OS_COUT);
		}

		AVM_OS_COUT << std::endl;
	}
	else
	{
		AVM_OS_COUT << "Unfound Execution Context by id: " << dbgIntValue
				<< " !!! Unchange current selection ..."
				<< std::endl << std::endl;
	}
}


void IDebugProcessorProvider::dbgCommandTrace()
{
	AVM_OS_COUT << "The user trace element :> ";
	mDebugTraceSequence.toStream(AVM_OS_COUT );
	AVM_OS_COUT << std::endl;
}

void IDebugProcessorProvider::dbgCommandTraceDetailLevel()
{
	if( not dbgCommandArg.empty() )
	{
		if( dbgCommandArg[0] == '-' )
		{
			dbgDetailsMin = not dbgDetailsMin;
		}
		else if( dbgCommandArg[0] == '+' )
		{
			dbgDetailsMed = not dbgDetailsMed;
		}
		else if( dbgCommandArg[0] == '*' )
		{
			dbgDetailsMax = not dbgDetailsMax;
		}
	}
	else
	{
		dbgDetailsMin = dbgDetailsMed = dbgDetailsMax = false;
	}

	AVM_OS_COUT << "detail :";
	if( dbgDetailsMin || dbgDetailsMed || dbgDetailsMax )
	{
		if( dbgDetailsMin ) { AVM_OS_COUT << " MINIMUM"; }
		if( dbgDetailsMed ) { AVM_OS_COUT << " MEDIUM" ; }
		if( dbgDetailsMax ) { AVM_OS_COUT << " MAXIMUM"; }
	}
	else
	{
		AVM_OS_COUT << " DEFAULT";
	}

	AVM_OS_COUT << std::endl << std::endl;
}



void IDebugProcessorProvider::dbgCommandVar()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedVariable == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a variable ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE, AVM_OPCODE_ASSIGN);

		if( dbgTracePoint->configureVariable(
				mDebugConfiguration, dbgCommandArg, mDebugSelectedVariables) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedVariable = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedVariables.add_unique( mDebugSelectedVariable );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedVariables.append(
						mDebugSelectedVariable = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound variable << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}


	if( mDebugSelectedVariable != nullptr )
	{
		AVM_OS_COUT << "Selected variable :> ";
		mDebugSelectedVariable->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			dbgEC = mDebugSelectedContext;
			do
			{
				AVM_OS_COUT << "With selected Context :> ";
				dbgEC->traceMinimum(AVM_OS_COUT);

				dbgPrintVarInfo( mDebugSelectedVariable );
			}
			while( mDebugTraceFullPathFlag &&
				((dbgEC = dbgEC->getPrevious()) != nullptr) );
		}

		AVM_OS_COUT << std::endl;
	}
}


void IDebugProcessorProvider::dbgPrintVarInfo(const TracePoint & aTP)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( dbgEC ) << "Execution Context !!!"
			<< SEND_EXIT;

	dbgED = dbgEC->getExecutionData();

	if( aTP.RID.valid() )
	{
		dbgValue = mDebugProcessor->getENV().getRvalue(dbgED,
				aTP.RID, aTP.object->to< InstanceOfData >() );
	}
	else
	{
		const ExecutableForm & anExecutable = aTP.getExecutable();
		if( anExecutable.isnotNullref() && anExecutable.hasInitialInstance() )
		{
			dbgValue = mDebugProcessor->getENV().getRvalue(
					dbgED, aTP.object->to< InstanceOfData >() );
		}
		else
		{
			dbgValue = BF::REF_NULL;
		}
	}

	if( dbgValue.valid() )
	{
		AVM_OS_COUT << " ==> var " << aTP.object->to_ptr< InstanceOfData >()->
				getTypeSpecifier().strT() << " " << aTP.object->getNameID()
				<< " = " << dbgValue.str() << std::endl;
	}
}

void IDebugProcessorProvider::dbgCommandVars()
{
	AVM_OS_COUT << "Selected variables :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedVariables);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedVariables )
		{
			dbgPrintVarInfo( itPoint);
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandTime()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedTimeVar == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a time variable ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_TIME_NATURE, AVM_OPCODE_TIMED_GUARD);
		dbgTracePoint->object = mDebugDeltaTimeVariable;

		if( dbgTracePoint->configureVariable(
				mDebugConfiguration, dbgCommandArg, mDebugSelectedVariables) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedTimeVar = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedVariables.add_unique( mDebugSelectedTimeVar );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedVariables.append(
						mDebugSelectedTimeVar = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound time variable << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedTimeVar != nullptr )
	{
		AVM_OS_COUT << "Selected time variable :> ";
		mDebugSelectedTimeVar->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintVarInfo( mDebugSelectedTimeVar );
		}

		AVM_OS_COUT << std::endl;
	}
}


void IDebugProcessorProvider::dbgCommandPort(
		ENUM_TRACE_POINT::TRACE_NATURE nature)
{
	if( (dbgCommandArg.empty() && (mDebugSelectedPort == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a port ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(nature, AVM_OPCODE_NULL);

		if( dbgTracePoint->configurePort(
				mDebugConfiguration, dbgCommandArg, mDebugSelectedPorts) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedPort = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedPorts.add_unique( mDebugSelectedPort );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedPorts.append(
						mDebugSelectedPort = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound port << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedPort != nullptr )
	{
		AVM_OS_COUT << "Selected port :> ";
		mDebugSelectedPort->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintPortInfo( mDebugSelectedPort );
		}

	}
}

void IDebugProcessorProvider::dbgPrintPortInfo(const TracePoint & aTP)
{

}

void IDebugProcessorProvider::dbgCommandPorts(
		ENUM_TRACE_POINT::TRACE_NATURE nature)
{
	AVM_OS_COUT << "Selected ports :> " << std::endl;
//	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedPorts);
	for( const auto & itPoint : mDebugSelectedPorts )
	{
		switch( nature )
		{
			case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
			case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
			case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
			case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
			{
				if( itPoint->nature == nature )
				{
					itPoint->toStream(AVM_OS_COUT);
				}
				break;
			}

			case ENUM_TRACE_POINT::TRACE_COM_NATURE:
			default:
			{
				itPoint->toStream(AVM_OS_COUT);

				break;
			}
		}
	}

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedPorts )
		{
			switch( nature )
			{
				case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
				case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
				case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
				case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
				{
					if( itPoint->nature == nature )
					{
						dbgPrintPortInfo( *itPoint );
					}
					break;
				}

				case ENUM_TRACE_POINT::TRACE_COM_NATURE:
				default:
				{
					dbgPrintPortInfo( *itPoint );

					break;
				}
			}
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandBuffer()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedBuffer == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a buffer ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_BUFFER_NATURE, AVM_OPCODE_NULL);

		if( dbgTracePoint->configureVariable(
				mDebugConfiguration, dbgCommandArg, mDebugSelectedVariables) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedBuffer = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedBuffers.add_unique( mDebugSelectedBuffer );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedBuffers.append(
						mDebugSelectedBuffer = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound buffer << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedBuffer != nullptr )
	{
		AVM_OS_COUT << "Selected buffer :> ";
		mDebugSelectedBuffer->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			dbgEC = mDebugSelectedContext;
			do
			{
				AVM_OS_COUT << "With selected Context :> ";
				dbgEC->traceMinimum(AVM_OS_COUT);

				dbgPrintBufferInfo( *mDebugSelectedBuffer );
			}
			while( mDebugTraceFullPathFlag &&
				((dbgEC = dbgEC->getPrevious()) != nullptr) );
		}

	}
}

void IDebugProcessorProvider::dbgPrintBufferInfo(TracePoint & aTP)
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( dbgEC ) << "Execution Context !!!"
			<< SEND_EXIT;

	dbgED = dbgEC->getExecutionData();

	if( aTP.RID.invalid() )
	{
		aTP.RID = dbgED.getRuntimeContainerRID(
				aTP.object->to_ptr< InstanceOfBuffer >() );
	}

	if( aTP.RID.valid() )
	{
		dbgRF = dbgED.ptrRuntime( aTP.RID );

		AVM_OS_COUT << " ==> buffer " << aTP.object->getNameID() << " = ";
		dbgRF->getBuffer(
				aTP.object->to_ptr< InstanceOfBuffer >() ).toStream(AVM_OS_COUT);
		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgCommandBuffers()
{
	AVM_OS_COUT << "Selected buffers :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedBuffers);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedBuffers )
		{
			dbgPrintBufferInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandMachine()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedMachine == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a machine ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_MACHINE_NATURE, AVM_OPCODE_RUN);

		if( dbgTracePoint->configureMachine(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedMachine = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedMachines.add_unique( mDebugSelectedMachine );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedMachines.append(
						mDebugSelectedMachine = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound machine << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedMachine != nullptr )
	{
		AVM_OS_COUT << "Selected machine :> ";
		mDebugSelectedMachine->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintMachineInfo( *mDebugSelectedMachine );
		}

		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgPrintMachineInfo(TracePoint & aTP)
{
	if( aTP.RID.invalid() )
	{
		aTP.RID = mDebugSelectedContext->getExecutionData().getRuntimeID(
				aTP.object->to< InstanceOfMachine >() );
	}

	if( aTP.RID.valid() )
	{
		dbgRF = mDebugSelectedContext->getExecutionData().ptrRuntime(aTP.RID);

		dbgRF->toStream(AVM_OS_COUT);
	}
}

void IDebugProcessorProvider::dbgCommandMachines()
{
	AVM_OS_COUT << "Selected machines :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedMachines);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( auto & itPoint : mDebugSelectedMachines )
		{
			dbgPrintMachineInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandParametersMachine()
{
	AVM_OS_COUT << "Parameters machine :> ";
	mDebugParametersMachine.toStream(AVM_OS_COUT);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

//		dbgPrintMachineInfo( & mDebugParametersMachine );

		if( dbgDetailsMax )
		{
			mDebugSelectedContext->getExecutionData().
					getParametersRuntimeForm().toStream(AVM_OS_COUT);
		}
		else if( dbgDetailsMed )
		{
			mDebugSelectedContext->getExecutionData().
					getParametersRuntimeForm().toStreamData(
						mDebugSelectedContext->getExecutionData(), AVM_OS_COUT);
		}
		else
		{
			mDebugSelectedContext->getExecutionData().
					getParametersRuntimeForm().toFscnData(AVM_OS_COUT,
							mDebugSelectedContext->getExecutionData(),
							RuntimeForm::nullref());
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandState()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedState == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a state ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_STATE_NATURE, AVM_OPCODE_RUN);

		if( dbgTracePoint->configureMachine(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedState = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedStates.add_unique( mDebugSelectedState );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedStates.append(
						mDebugSelectedState = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound state << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedState != nullptr )
	{
		AVM_OS_COUT << "Selected state :> ";
		mDebugSelectedState->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintStateInfo( *mDebugSelectedState );
		}

		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgPrintStateInfo(TracePoint & aTP)
{
	dbgPrintMachineInfo( aTP );
}

void IDebugProcessorProvider::dbgCommandStates()
{
	AVM_OS_COUT << "Selected states :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedStates);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( auto & itPoint : mDebugSelectedStates )
		{
			dbgPrintStateInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandStatemachine()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedStatemachine == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a statemachine ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE, AVM_OPCODE_RUN);

		if( dbgTracePoint->configureMachine(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedStatemachine = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedStatemachines.add_unique( mDebugSelectedStatemachine );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedStatemachines.append(
						mDebugSelectedStatemachine = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound statemachine << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedStatemachine != nullptr )
	{
		AVM_OS_COUT << "Selected statemachine :> ";
		mDebugSelectedStatemachine->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintStatemachineInfo( *mDebugSelectedStatemachine );
		}

		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgPrintStatemachineInfo(TracePoint & aTP)
{
	dbgPrintMachineInfo( aTP );
}

void IDebugProcessorProvider::dbgCommandStatemachines()
{
	AVM_OS_COUT << "Selected statemachines :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedStatemachines);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( auto & itPoint : mDebugSelectedStatemachines )
		{
			dbgPrintStatemachineInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandTransition()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedTransition == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a transition ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
				AVM_OPCODE_INVOKE_TRANSITION);

		if( dbgTracePoint->configureTransition(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedTransition = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedTransitions.add_unique( mDebugSelectedTransition );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedTransitions.append(
						mDebugSelectedTransition = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound transition << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedTransition != nullptr )
	{
		AVM_OS_COUT << "Selected transition :> ";
		mDebugSelectedTransition->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintTransitionInfo( mDebugSelectedTransition );
		}

		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgPrintTransitionInfo(const TracePoint & aTP)
{
	const AvmTransition * aTransition = aTP.object->to_ptr< AvmTransition >();

	if( dbgDetailsMax && (mDebugSelectedContext != nullptr) )
	{
		AVM_OS_COUT << AVM_TAB_INDENT;

		aTransition->toStreamHeader(AVM_OS_COUT);
		if( aTransition->hasInternalCommunicationCode() )
		{
			AVM_OS_COUT << " ";
			ObjectElement::toStreamStaticCom(AVM_OS_COUT,
					aTransition->getInternalCommunicationCode());
		}
		AVM_OS_COUT << std::endl;
	}

	else if( dbgDetailsMed )
	{
		aTP.object->toStream(AVM_OS_COUT);
	}
	else
	{
		aTransition->toStreamHeader(AVM_OS_COUT);
		AVM_OS_COUT << std::endl;
	}
}

void IDebugProcessorProvider::dbgCommandTransitions()
{
	AVM_OS_COUT << "Selected transitions :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedTransitions);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedTransitions )
		{
			dbgPrintTransitionInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandRoutine()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedRoutine == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a routine ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE, AVM_OPCODE_NULL);

		if( dbgTracePoint->configureRoutine(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedRoutine = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedRoutines.add_unique( mDebugSelectedRoutine );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedRoutines.append(
						mDebugSelectedRoutine = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound routine << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedRoutine != nullptr )
	{
		AVM_OS_COUT << "Selected routine :> ";
		mDebugSelectedRoutine->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintRoutineInfo( mDebugSelectedRoutine );
		}

	}
}

void IDebugProcessorProvider::dbgPrintRoutineInfo(const TracePoint & aTP)
{

}

void IDebugProcessorProvider::dbgCommandRoutines()
{
	AVM_OS_COUT << "Selected routines :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedRoutines);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedRoutines )
		{
			dbgPrintRoutineInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandRunnable()
{
	if( (dbgCommandArg.empty() && (mDebugSelectedRunnable == nullptr)) ||
		(dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a runnable ID :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else
	{
		if( dbgCommandArg[0] == '?' )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}
	}

	if( not dbgCommandArg.empty() )
	{
		dbgTP = dbgTracePoint = new TracePoint(
				ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE, AVM_OPCODE_NULL);

		if( dbgTracePoint->configureRunnable(mDebugConfiguration, dbgCommandArg) )
		{
			if( mDebugTraceSequence.containsPoint(dbgTracePoint, dbgTP) )
			{
				mDebugSelectedRunnable = dbgTP.to_ptr< TracePoint >();

				mDebugSelectedRunnables.add_unique( mDebugSelectedRunnable );
			}
			else
			{
				dbgTracePoint->tpid = ++(mDebugTraceFactory->TP_ID);

				mDebugTraceSequence.points.append( dbgTP );

				mDebugSelectedRunnables.append(
						mDebugSelectedRunnable = dbgTracePoint );
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound runnable << " << dbgCommandArg << " >> !"
					<< std::endl;
		}
	}

	if( mDebugSelectedRunnable != nullptr )
	{
		AVM_OS_COUT << "Selected runnable :> ";
		mDebugSelectedRunnable->toStream(AVM_OS_COUT);

		if( mDebugSelectedContext != nullptr )
		{
			AVM_OS_COUT << "With selected Context :> ";
			mDebugSelectedContext->debugDefault(AVM_OS_COUT);

			dbgPrintRunnableInfo( mDebugSelectedRunnable );
		}

	}
}

void IDebugProcessorProvider::dbgPrintRunnableInfo(const TracePoint & aTP)
{

}

void IDebugProcessorProvider::dbgCommandRunnables()
{
	AVM_OS_COUT << "Selected runnables :> " << std::endl;
	mDebugTraceFactory->toStream(AVM_OS_COUT, mDebugSelectedRunnables);

	if( mDebugSelectedContext != nullptr )
	{
		AVM_OS_COUT << "With selected Context :> ";
		mDebugSelectedContext->debugDefault(AVM_OS_COUT);

		for( const auto & itPoint : mDebugSelectedRunnables )
		{
			dbgPrintRunnableInfo( *itPoint );
		}
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandEcho()
{
	StringTools::replaceAllEscapeSequences(dbgCommandArg);

	if( (dbgCommandArg.size() > 2) && (
		((dbgCommandArg[0] == '"') &&
				(dbgCommandArg[dbgCommandArg.size() - 1] == '"')) ||
		((dbgCommandArg[0] == '\'') &&
				(dbgCommandArg[dbgCommandArg.size() - 1] == '\'')) ) )
	{
		dbgCommandArg = dbgCommandArg.substr( 1 , dbgCommandArg.size() - 2 );
	}

	AVM_OS_COUT << dbgCommandArg;
}

void IDebugProcessorProvider::dbgCommandPrint()
{
	dbgCommandEcho();
}

void IDebugProcessorProvider::dbgCommandShow()
{
	dbgCommandEcho();
}



void IDebugProcessorProvider::dbgCommandEnableDisableProcess(bool bStatus)
{
	if( dbgCommandArg.empty() )
	{
	}

	else
	{
		if( dbgCommandArg == "?" )
		{
			AVM_OS_COUT << "Select a process { prefilter , "
					"postfilter , preprocess , postprocess } :> ";

			std::getline(std::cin, dbgCommandArg);
			StringTools::ltrim( dbgCommandArg );
		}
		else if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
		{
			StringTools::ltrim( dbgCommandArg , 1 );
		}

		if( dbgCommandArg.find("all") != std::string::npos )
		{
			mDebugPrefilteringFlag = bStatus;
			mDebugPrefilteringFinalizeFlag = bStatus;

			mDebugPostfilteringFlag = bStatus;
			mDebugPostfilteringFinalizeFlag = bStatus;

			mDebugPreprocessingFlag = bStatus;
			mDebugPreprocessingInitializeFlag = bStatus;
			mDebugPreprocessingFinalizeFlag   = bStatus;

			mDebugPostprocessingFlag = bStatus;
			mDebugPostprocessingInitializeFlag = bStatus;
			mDebugPostprocessingFinalizeFlag   = bStatus;
		}

		else if( dbgCommandArg.find("prefilter#finalize") != std::string::npos )
		{
			mDebugPrefilteringFinalizeFlag = bStatus;
		}
		else if( dbgCommandArg.find("prefilter") != std::string::npos )
		{
			mDebugPrefilteringFlag = bStatus;

			mDebugProcessor->enablePrefilter( bStatus );
		}

		else if( dbgCommandArg.find("postfilter#finalize") != std::string::npos )
		{
			mDebugPostfilteringFinalizeFlag = bStatus;
		}
		else if( dbgCommandArg.find("postfilter") != std::string::npos )
		{
			mDebugPostfilteringFlag = bStatus;

			mDebugProcessor->enablePostfilter( bStatus );
		}

		else if( dbgCommandArg.find("preprocess") != std::string::npos )
		{
			if( dbgCommandArg.find("initialize") != std::string::npos )
			{
				mDebugPreprocessingInitializeFlag = bStatus;
			}
			else if( dbgCommandArg.find("finalize") != std::string::npos )
			{
				mDebugPreprocessingFinalizeFlag = bStatus;
			}
			else
			{
				mDebugPreprocessingFlag = bStatus;
				mDebugPreprocessingInitializeFlag = bStatus;
				mDebugPreprocessingFinalizeFlag   = bStatus;

				mDebugProcessor->enablePreprocess( bStatus );
			}
		}
		else if( dbgCommandArg.find("postprocess") != std::string::npos )
		{
			if( dbgCommandArg.find("initialize") != std::string::npos )
			{
				mDebugPostprocessingInitializeFlag = bStatus;
			}
			else if( dbgCommandArg.find("finalize") != std::string::npos )
			{
				mDebugPostprocessingFinalizeFlag = bStatus;
			}
			else
			{
				mDebugPostprocessingFlag = bStatus;
				mDebugPostprocessingInitializeFlag = bStatus;
				mDebugPostprocessingFinalizeFlag   = bStatus;

				mDebugProcessor->enablePostprocess( bStatus );
			}
		}
	}


	if( bStatus  )
	{
		AVM_OS_COUT << "The debug< enable > processes are :> "
				<< ( mDebugPrefilteringFlag ?          " prefilter" : "" )
				<< ( mDebugPrefilteringFinalizeFlag ?  " prefilter#finalize" : "" )
				<< ( mDebugPostfilteringFlag ?         " postfilter" : "" )
				<< ( mDebugPostfilteringFinalizeFlag ? " postfilter#finalize" : "" )
				<< ( mDebugPreprocessingFlag ?         " preprocess" : "" )
				<< ( mDebugPostprocessingFlag ?        " postprocess" : "" )
				<< std::endl;
	}
	else
	{
		AVM_OS_COUT << "The debug< disable > processes are :> "
				<< ( mDebugPrefilteringFlag ?          "" : " prefilter" )
				<< ( mDebugPrefilteringFinalizeFlag ?  "" : " prefilter#finalize" )
				<< ( mDebugPostfilteringFlag ?         "" : " postfilter" )
				<< ( mDebugPostfilteringFinalizeFlag ? "" : " postfilter#finalize" )
				<< ( mDebugPreprocessingFlag ?         "" : " preprocess" )
				<< ( mDebugPostprocessingFlag ?        "" : " postprocess" )
				<< std::endl;
	}

	AVM_OS_COUT << std::endl;
}


void IDebugProcessorProvider::dbgCommandVerbosityLevel()
{
	if( (not dbgCommandArg.empty()) && (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a verbosity level "
				"{ SILENT , MINIMUM , MEDIUM , MAXIMUM } :> ";

		std::getline(std::cin, dbgCommandArg);
	}
	else if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
	{
		StringTools::ltrim( dbgCommandArg , 1 );
	}

	avm_setExecVerbosityLevel( dbgCommandArg );

	AVM_OS_COUT << "Verbosity level :> " << avm_strExecVerbosityLevel()
			<< std::endl << std::endl;
}


void IDebugProcessorProvider::dbgCommandDebugLevel()
{
	if( (not dbgCommandArg.empty()) && (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a debug level "
				"{ ZERO , LOW , MEDIUM , HIGH , ULTRA } :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}
	else if( (dbgCommandArg[0] == '#') || (dbgCommandArg[0] == '?') )
	{
		StringTools::ltrim( dbgCommandArg , 1 );
	}

	avm_setDebugLevel( dbgCommandArg );

	AVM_OS_COUT << "Debug trace level :> " << avm_strDebugLevel()
			<< std::endl << std::endl;
}


void IDebugProcessorProvider::dbgCommandDebugFlag(bool bStatus)
{
	if( (not dbgCommandArg.empty()) && (dbgCommandArg == "?") )
	{
		AVM_OS_COUT << "Enter a debug flag "
				"{ COMPUTING , PROGRAM , STATEMENT , BYTECODE , ... } :> ";

		std::getline(std::cin, dbgCommandArg);
		StringTools::ltrim( dbgCommandArg );
	}

	if( bStatus )
	{
		avm_setDebugFlag( dbgCommandArg );
	}
	else
	{
		avm_unsetDebugFlag( dbgCommandArg );
	}

	AVM_OS_COUT << "Debug trace flag :> " << avm_strDebugFlag(" | ")
			<< std::endl << std::endl;
}


} /* namespace sep */
