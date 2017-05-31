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

#ifndef IDEBUGPROCESSORPROVIDER_H_
#define IDEBUGPROCESSORPROVIDER_H_

#include <util/avm_string.h>

#include <collection/Typedef.h>

#include <fam/api/AbstractProcessorUnit.h>

#include <fml/runtime/ExecutionData.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <sew/Configuration.h>

#include <fstream>


namespace sep
{

class Configuration;

class ExecutionContext;

class InstanceOfData;

class RuntimeForm;

class TraceFactory;



class IDebugProcessorProvider
{


protected:
	/**
	 * ATTRIBUTES
	 */
	AbstractProcessorUnit * mDebugProcessor;
	Configuration & mDebugConfiguration;

	bool mDebugEnabledFlag;
	bool mDebugConsoleFlag;

	std::string mDebugScriptFile;

	std::string mDebugPromptPrefix;

	bool mDebugFilteringDetailFlag;
	bool mDebugFilteringInitializeFlag;
	bool mDebugFilteringFinalizeFlag;

	bool mDebugPrefilteringFlag;
	bool mDebugPrefilteringDetailFlag;
	bool mDebugPrefilteringFinalizeFlag;

	bool mDebugPostfilteringFlag;
	bool mDebugPostfilteringDetailFlag;
	bool mDebugPostfilteringFinalizeFlag;

	bool mDebugPreprocessingFlag;
	bool mDebugPreprocessingDetailFlag;

	bool mDebugPostprocessingFlag;
	bool mDebugPostprocessingDetailFlag;

	avm_size_t mDebugEvalStepCount;
	avm_size_t mDebugBreakpointEvalStep;
	avm_size_t mDebugBreakpointEvalStepPeriod;

	avm_size_t mDebugBreakpointEvalContext;

	const ExecutionContext * mDebugSelectedContext;
	bool mDebugTraceFullPathFlag;

	TraceSequence mDebugTraceSequence;

	TracePoint * mDebugSelectedVar;
	ListOfTracePoint mDebugSelectedVars;

	TracePoint * mDebugSelectedTimeVar;

	TracePoint * mDebugSelectedPort;
	ListOfTracePoint mDebugSelectedPorts;

	TracePoint * mDebugSelectedBuffer;
	ListOfTracePoint mDebugSelectedBuffers;

	TracePoint mDebugParametersMachine;

	TracePoint * mDebugSelectedMachine;
	ListOfTracePoint mDebugSelectedMachines;

	TracePoint * mDebugSelectedState;
	ListOfTracePoint mDebugSelectedStates;

	TracePoint * mDebugSelectedStatemachine;
	ListOfTracePoint mDebugSelectedStatemachines;

	TracePoint * mDebugSelectedTransition;
	ListOfTracePoint mDebugSelectedTransitions;

	TracePoint * mDebugSelectedRoutine;
	ListOfTracePoint mDebugSelectedRoutines;

	TracePoint * mDebugSelectedRunnable;
	ListOfTracePoint mDebugSelectedRunnables;

	// Trace Factory tools
	TraceFactory * mDebugTraceFactory;
	InstanceOfData   * mDebugTimeVariable;
	InstanceOfData   * mDebugDeltaTimeVariable;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	BF dbgTP;
	TracePoint * dbgTracePoint;
	ListOfTracePoint::iterator dbgPointIt;
	ListOfTracePoint::iterator dbgPointItEnd;

	ListOfExecutionContext * dbgQueue;
	ListOfExecutionContext::iterator dbgQueueIt;
	ListOfExecutionContext::iterator dbgQueueItEnd;

	bool dbgContinueREPL;

	bool dbgDetailsMin;
	bool dbgDetailsMed;
	bool dbgDetailsMax;

	bool dbgDecodeCommandOk;

	VectorOfString dbgCommandLineHistory;
	std::string dbgCommandLine;
	std::string dbgCommandArg;

	avm_integer_t dbgIntValue;
	avm_size_t dbgOffset;

	const ExecutionContext * dbgEC;
	APExecutionData dbgED;
	const RuntimeForm * dbgRF;
	BF dbgValue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IDebugProcessorProvider(AbstractProcessorUnit * aProcessor)
	: mDebugProcessor( aProcessor ),
	mDebugConfiguration( aProcessor->getConfiguration() ),
	mDebugEnabledFlag( false ),

	mDebugConsoleFlag( true ),
	mDebugScriptFile( ),

	mDebugPromptPrefix( ),

	mDebugFilteringDetailFlag( false ),
	mDebugFilteringInitializeFlag( false ),
	mDebugFilteringFinalizeFlag( false ),

	mDebugPrefilteringFlag( false ),
	mDebugPrefilteringDetailFlag( false ),
	mDebugPrefilteringFinalizeFlag( false ),

	mDebugPostfilteringFlag( false ),
	mDebugPostfilteringDetailFlag( false ),
	mDebugPostfilteringFinalizeFlag( false ),

	mDebugPreprocessingFlag( false ),
	mDebugPreprocessingDetailFlag( false ),

	mDebugPostprocessingFlag( false ),
	mDebugPostprocessingDetailFlag( false ),

	mDebugEvalStepCount( 0 ),
	mDebugBreakpointEvalStep( 0 ),
	mDebugBreakpointEvalStepPeriod( 0 ),

	mDebugBreakpointEvalContext( 0 ),

	mDebugSelectedContext( NULL ),

	mDebugTraceFullPathFlag( false ),

	mDebugTraceSequence( ),

	mDebugSelectedVar( NULL ),
	mDebugSelectedVars( ),

	mDebugSelectedTimeVar( NULL ),

	mDebugSelectedPort( NULL ),
	mDebugSelectedPorts( ),

	mDebugSelectedBuffer( NULL ),
	mDebugSelectedBuffers( ),

	mDebugParametersMachine( ENUM_TRACE_POINT::TRACE_MACHINE_NATURE ),

	mDebugSelectedMachine( NULL ),
	mDebugSelectedMachines( ),

	mDebugSelectedState( NULL ),
	mDebugSelectedStates( ),

	mDebugSelectedStatemachine( NULL ),
	mDebugSelectedStatemachines( ),

	mDebugSelectedTransition( NULL ),
	mDebugSelectedTransitions( ),

	mDebugSelectedRoutine( NULL ),
	mDebugSelectedRoutines( ),

	mDebugSelectedRunnable( NULL ),
	mDebugSelectedRunnables( ),

	// Trace Factory tools
	mDebugTraceFactory( NULL ),
	mDebugTimeVariable( NULL ),
	mDebugDeltaTimeVariable( NULL ),

	dbgTP( ),
	dbgTracePoint( NULL ),
	dbgPointIt( ),
	dbgPointItEnd( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	dbgQueue( NULL ),
	dbgQueueIt( ),
	dbgQueueItEnd( ),

	dbgContinueREPL( true ),

	dbgDetailsMin( false ),
	dbgDetailsMed( false ),
	dbgDetailsMax( false ),

	dbgDecodeCommandOk( false ),

	dbgCommandLineHistory( "help" ),
	dbgCommandLine( ),
	dbgCommandArg( ),

	dbgIntValue( 0 ),
	dbgOffset( 0 ),

	dbgEC( NULL ),
	dbgED( ),
	dbgRF( NULL ),
	dbgValue( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~IDebugProcessorProvider();


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// PLUGIN PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugConfigureImpl(WObject * wfParameterObject);

	/**
	 * TEST
	 */
	inline bool isDebugEnabled() const
	{
		return( mDebugFilteringInitializeFlag || mDebugFilteringFinalizeFlag ||
				mDebugPrefilteringFlag  || mDebugPrefilteringFinalizeFlag    ||
				mDebugPostfilteringFlag || mDebugPostfilteringFinalizeFlag   ||
				mDebugPreprocessingFlag || mDebugPostprocessingFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugPreprocessing();

	virtual bool debugPreprocessing(const ExecutionContext * anEC);

	inline bool isDebugPreprocessing() const
	{
		return( mDebugPreprocessingFlag );
	}


	virtual bool debugPostprocessing();

	virtual bool debugPostprocessing(const ExecutionContext * anEC);

	inline bool isDebugPostprocessing() const
	{
		return( mDebugPostprocessingFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	bool debugActivatorTriggering();


	bool debugFilteringInitialize();

	bool debugFilteringInitialize(const ExecutionContext * anEC);

	inline bool isDebugFilteringInitialize()
	{
		return( mDebugFilteringInitializeFlag );
	}


	bool debugFilteringFinalize();

	bool debugFilteringFinalize(const ExecutionContext * anEC);

	inline bool isDebugFilteringFinalize()
	{
		return( mDebugFilteringFinalizeFlag );
	}


	virtual bool debugPrefiltering();
	virtual bool debugPrefiltering(const ExecutionContext * anEC);

	inline bool isDebugPrefiltering() const
	{
		return( mDebugPrefilteringFlag );
	}


	bool debugPrefilteringFinalize();

	inline bool isDebugPrefilteringFinalize()
	{
		return( mDebugPrefilteringFinalizeFlag );
	}


	virtual bool debugPostfiltering();
	virtual bool debugPostfiltering(const ExecutionContext * anEC);

	inline bool isDebugPostfiltering() const
	{
		return( mDebugPostfilteringFlag );
	}


	bool debugPostfilteringFinalize();

	inline bool isDebugPostfilteringFinalize()
	{
		return( mDebugPostfilteringFinalizeFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING
	////////////////////////////////////////////////////////////////////////////

	void debugReadEvalCommand();


	void debugReadEvalScript();

	bool isDebugScript(std::ifstream & aScriptStream);

	void debugReadEvalScript(std::ifstream & aScriptStream);


	void debugReadEvalCommandLoop();

	void debugReadHistoryCommand();

	void debugEvalCommand();

	/**
	 * API
	 * if return false,
	 * the default debug evaluation command will handle the current command
	 */
	virtual bool debugEvalCommandImpl() = 0;

	/**
	 * method for launch anywhere the REPL command loop !
	 */
	inline void debugReadEvalCommandPrintLoop(
			const std::string & aDebugPromptPrefix = "PROCESSOR#CTX",
			ExecutionContext * aDebugSelectedContext = NULL)
	{
		mDebugPromptPrefix = aDebugPromptPrefix;

		if( aDebugSelectedContext != NULL )
		{
			mDebugPromptPrefix = aDebugPromptPrefix;
		}

		debugReadEvalCommand();
	}


	/**
	 * Command decoder
	 */
	inline bool isDebugStringCommand(const std::string & cmdString)
	{
		if( StringTools::startsWith(dbgCommandLine, cmdString) )
		{
			StringTools::ltrim( dbgCommandArg , cmdString.size());

			return( dbgDecodeCommandOk = true );
		}

		return( false );
	}

	inline bool isDebugCharCommand(char cmdChar)
	{
		if( ((not dbgCommandLine.empty()) && (dbgCommandLine[0] == cmdChar)) &&
			((dbgCommandLine.size() == 1) || (not ::isalpha(dbgCommandLine[1]))) )
		{
			StringTools::ltrim( dbgCommandArg , 1 );

			return( dbgDecodeCommandOk = true );
		}

		return( false );
	}


	void dbgCheckCommandDetailsArg();


	inline bool dbgDecodeCommand(const std::string & cmdStr)
	{
		if( isDebugStringCommand(cmdStr) )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(const std::string & cmdStr, char cmdChar)
	{
		if( isDebugStringCommand(cmdStr) || isDebugCharCommand(cmdChar) )
		{
			dbgCheckCommandDetailsArg() ;

			dbgDecodeCommandOk = true;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(
			const std::string & cmdStr, const std::string & cmdStr1)
	{
		if( isDebugStringCommand(cmdStr) || isDebugStringCommand(cmdStr1) )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(const std::string & cmdStr,
			const std::string & cmdStr1, const std::string & cmdStr2)
	{
		if( isDebugStringCommand(cmdStr) || isDebugStringCommand(cmdStr1) ||
			isDebugStringCommand(cmdStr2) )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(
			const std::string & cmdStr, const std::string & cmdStr1,
			const std::string & cmdStr2, const std::string & cmdStr3)
	{
		if( isDebugStringCommand(cmdStr)  || isDebugStringCommand(cmdStr1) ||
			isDebugStringCommand(cmdStr2) || isDebugStringCommand(cmdStr3) )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(const std::string & cmdStr,
			const std::string & cmdStr1, char cmdChar)
	{
		if( isDebugStringCommand(cmdStr) || isDebugStringCommand(cmdStr1) ||
			isDebugCharCommand(cmdChar)  )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}

	inline bool dbgDecodeCommand(
			const std::string & cmdStr, char cmdChar, char cmdChar1)
	{
		if( isDebugStringCommand(cmdStr) ||
			isDebugCharCommand(cmdChar)  || isDebugCharCommand(cmdChar1) )
		{
			dbgCheckCommandDetailsArg() ;
		}

		return( dbgDecodeCommandOk );
	}


	static std::string DEBUG_SHELL_COMMAND_SUMMARY;

	static std::string DEBUG_SHELL_COMMAND_HISTORY;

	static std::string DEBUG_SHELL_COMMAND_CONTROL;

	static std::string DEBUG_SHELL_COMMAND_QUEUE;

	static std::string DEBUG_SHELL_COMMAND_CONTEX;

	static std::string DEBUG_SHELL_COMMAND_DATA;

	static std::string DEBUG_SHELL_COMMAND_PRINT;

	static std::string DEBUG_SHELL_COMMAND_REPORT;

	static std::string DEBUG_SHELL_COMMAND_BREAKPOINT;

	static std::string DEBUG_SHELL_COMMAND_OPTION;

	static std::string DEBUG_SHELL_COMMAND_LOG;



	void dbgCommandHelp();

	void dbgCommandHistory();


	void dbgCommandConfig();

	void dbgCommandBreak();

	void dbgCommandNext();

	void dbgCommandPeriod();

	void dbgCommandQueue();

	void dbgCommandContext();

	void dbgCommandPath();

	void dbgCommandTrace();

	void dbgCommandTraceDetailLevel();

	void dbgPrintVarInfo(TracePoint * aTP);
	void dbgCommandVar();
	void dbgCommandVars();

	void dbgCommandTime();

	void dbgPrintPortInfo(TracePoint * aTP);
	void dbgCommandPort(ENUM_TRACE_POINT::TRACE_NATURE nature);
	void dbgCommandPorts(ENUM_TRACE_POINT::TRACE_NATURE nature);

	void dbgPrintBufferInfo(TracePoint * aTP);
	void dbgCommandBuffer();
	void dbgCommandBuffers();

	void dbgPrintMachineInfo(TracePoint * aTP);
	void dbgCommandMachine();
	void dbgCommandMachines();

	void dbgCommandParametersMachine();

	void dbgPrintStateInfo(TracePoint * aTP);
	void dbgCommandState();
	void dbgCommandStates();

	void dbgPrintStatemachineInfo(TracePoint * aTP);
	void dbgCommandStatemachine();
	void dbgCommandStatemachines();

	void dbgPrintTransitionInfo(TracePoint * aTP);
	void dbgCommandTransition();
	void dbgCommandTransitions();

	void dbgPrintRoutineInfo(TracePoint * aTP);
	void dbgCommandRoutine();
	void dbgCommandRoutines();

	void dbgPrintRunnableInfo(TracePoint * aTP);
	void dbgCommandRunnable();
	void dbgCommandRunnables();

	void dbgCommandEcho();
	void dbgCommandPrint();
	void dbgCommandShow();

	void dbgCommandEnableDisableProcess(bool bStatus);

	void dbgCommandVerbosityLevel();

	void dbgCommandDebugLevel();

	void dbgCommandDebugFlag(bool bStatus);

};


} /* namespace sep */

#endif /* IDEBUGPROCESSORPROVIDER_H_ */
