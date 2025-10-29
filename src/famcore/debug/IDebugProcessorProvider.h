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

#include "IDebugProcessorHelper.h"

#include <collection/Typedef.h>

#include  <famcore/api/AbstractProcessorUnit.h>

#include <fml/runtime/ExecutionData.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <sew/Configuration.h>


namespace sep
{

class Configuration;

class ExecutionContext;

class InstanceOfData;

class RuntimeForm;

class TraceFactory;



class IDebugProcessorProvider  :  public IDebugProcessorHelper
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
	bool mDebugPreFilteringInitializeFlag;
	bool mDebugPrefilteringFinalizeFlag;

	bool mDebugPostfilteringFlag;
	bool mDebugPostfilteringDetailFlag;
	bool mDebugPostFilteringInitializeFlag;
	bool mDebugPostfilteringFinalizeFlag;

	bool mDebugPreprocessingFlag;
	bool mDebugPreprocessingDetailFlag;
	bool mDebugPreprocessingInitializeFlag;
	bool mDebugPreprocessingFinalizeFlag;

	bool mDebugPostprocessingFlag;
	bool mDebugPostprocessingDetailFlag;
	bool mDebugPostprocessingInitializeFlag;
	bool mDebugPostprocessingFinalizeFlag;

	std::size_t mDebugEvalStepCount;
	std::size_t mDebugBreakpointEvalStep;
	std::size_t mDebugBreakpointEvalStepPeriod;

	std::size_t mDebugBreakpointEvalContext;

	const ExecutionContext * mDebugSelectedContext;
	bool mDebugTraceFullPathFlag;

	TraceSequence mDebugTraceSequence;

	TracePoint * mDebugSelectedVariable;
	ListOfTracePoint mDebugSelectedVariables;

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

	ListOfExecutionContext dbgLeafEC;

	ListOfExecutionContext * dbgQueue;

	bool dbgContinueREPL;

	bool dbgDetailsMin;
	bool dbgDetailsMed;
	bool dbgDetailsMax;

	bool dbgDecodeCommandOk;

	VectorOfString dbgCommandLineHistory;
	std::string dbgCommandLine;
	std::string dbgCommandArg;

	avm_integer_t dbgIntValue;
	std::size_t dbgOffset;

	const ExecutionContext * dbgEC;
	ExecutionData dbgED;
	const RuntimeForm * dbgRF;
	BF dbgValue;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IDebugProcessorProvider(AbstractProcessorUnit * aProcessor)
	: IDebugProcessorHelper( ),
	mDebugProcessor( aProcessor ),
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
	mDebugPreFilteringInitializeFlag( false ),
	mDebugPrefilteringFinalizeFlag( false ),

	mDebugPostfilteringFlag( false ),
	mDebugPostfilteringDetailFlag( false ),
	mDebugPostFilteringInitializeFlag( false ),
	mDebugPostfilteringFinalizeFlag( false ),

	mDebugPreprocessingFlag( false ),
	mDebugPreprocessingDetailFlag( false ),
	mDebugPreprocessingInitializeFlag( false ),
	mDebugPreprocessingFinalizeFlag( false ),

	mDebugPostprocessingFlag( false ),
	mDebugPostprocessingDetailFlag( false ),
	mDebugPostprocessingInitializeFlag( false ),
	mDebugPostprocessingFinalizeFlag( false ),

	mDebugEvalStepCount( 0 ),
	mDebugBreakpointEvalStep( 0 ),
	mDebugBreakpointEvalStepPeriod( 0 ),

	mDebugBreakpointEvalContext( 0 ),

	mDebugSelectedContext( nullptr ),

	mDebugTraceFullPathFlag( false ),

	mDebugTraceSequence( ),

	mDebugSelectedVariable( nullptr ),
	mDebugSelectedVariables( ),

	mDebugSelectedTimeVar( nullptr ),

	mDebugSelectedPort( nullptr ),
	mDebugSelectedPorts( ),

	mDebugSelectedBuffer( nullptr ),
	mDebugSelectedBuffers( ),

	mDebugParametersMachine( ENUM_TRACE_POINT::TRACE_MACHINE_NATURE ),

	mDebugSelectedMachine( nullptr ),
	mDebugSelectedMachines( ),

	mDebugSelectedState( nullptr ),
	mDebugSelectedStates( ),

	mDebugSelectedStatemachine( nullptr ),
	mDebugSelectedStatemachines( ),

	mDebugSelectedTransition( nullptr ),
	mDebugSelectedTransitions( ),

	mDebugSelectedRoutine( nullptr ),
	mDebugSelectedRoutines( ),

	mDebugSelectedRunnable( nullptr ),
	mDebugSelectedRunnables( ),

	// Trace Factory tools
	mDebugTraceFactory( nullptr ),
	mDebugTimeVariable( nullptr ),
	mDebugDeltaTimeVariable( nullptr ),

	dbgTP( ),
	dbgTracePoint( nullptr ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	dbgQueue( nullptr ),

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

	dbgEC( nullptr ),
	dbgED( ),
	dbgRF( nullptr ),
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

	virtual bool debugConfigureImpl(const WObject * wfParameterObject);

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
	// PRE-PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugPreprocessing();

	inline virtual bool debugPreprocessingInitialize()
	{
		if( mDebugPreprocessingInitializeFlag )
		{
			mDebugPromptPrefix = "PRE-PROCESSING-INIT";

			return debugPreprocessing();
		}

		return( true );
	}

	inline virtual bool debugPreprocessingFinalize()
	{
		if( mDebugPreprocessingFinalizeFlag )
		{
			mDebugPromptPrefix = "PRE-PROCESSING-FINAL";

			return debugPreprocessing();
		}

		return( true );
	}

	virtual bool debugPreprocessing(const ExecutionContext * anEC);

	inline bool isDebugPreprocessing() const
	{
		return( mDebugPreprocessingFlag );
	}

	inline bool isDebugPreprocessingInitialize() const
	{
		return( mDebugPreprocessingInitializeFlag );
	}

	inline bool isDebugPreprocessingFinalize() const
	{
		return( mDebugPreprocessingFinalizeFlag );
	}


	////////////////////////////////////////////////////////////////////////////
	// POST-PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugPostprocessing();

	inline virtual bool debugPostprocessingInitialize()
	{
		if( mDebugPostprocessingInitializeFlag )
		{
			mDebugPromptPrefix = "POST-PROCESSING-INIT";

			return debugPostprocessing();
		}

		return( true );
	}

	virtual bool debugPostprocessingFinalize()
	{
		if( mDebugPostprocessingFinalizeFlag )
		{
			mDebugPromptPrefix = "POST-PROCESSING-FINAL";

			return debugPostprocessing();
		}

		return( true );
	}

	virtual bool debugPostprocessing(const ExecutionContext * anEC);

	inline bool isDebugPostprocessing() const
	{
		return( mDebugPostprocessingFlag );
	}

	inline bool isDebugPostprocessingInitialize() const
	{
		return( mDebugPostprocessingInitializeFlag );
	}

	inline bool isDebugPostprocessingFinalize() const
	{
		return( mDebugPostprocessingFinalizeFlag );
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

	inline bool isDebugPrefilteringInitialize() const
	{
		return( mDebugPreFilteringInitializeFlag );
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

	inline bool isDebugPostfilteringInitialize()
	{
		return( mDebugPostFilteringInitializeFlag );
	}

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
			const std::string & aDebugPromptPrefix = "PROCESSOR-CTX",
			ExecutionContext * aDebugSelectedContext = nullptr)
	{
		mDebugPromptPrefix = aDebugPromptPrefix;

		if( aDebugSelectedContext != nullptr )
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
		if( dbgCommandLine.starts_with(cmdString) )
		{
			dbgCommandArg = dbgCommandLine;

			StringTools::ltrim( dbgCommandArg , cmdString.size());
			StringTools::rtrim( dbgCommandArg );

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
			StringTools::rtrim( dbgCommandArg );

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

	void dbgCommandLeavesContexts();

	void dbgCommandPath();

	void dbgCommandTrace();

	void dbgCommandTraceDetailLevel();

	void dbgPrintVarInfo(const TracePoint & aTP);
	void dbgCommandVar();
	void dbgCommandVars();

	void dbgCommandTime();

	void dbgPrintPortInfo(const TracePoint & aTP);
	void dbgCommandPort(ENUM_TRACE_POINT::TRACE_NATURE nature);
	void dbgCommandPorts(ENUM_TRACE_POINT::TRACE_NATURE nature);

	void dbgPrintBufferInfo(TracePoint & aTP);
	void dbgCommandBuffer();
	void dbgCommandBuffers();

	void dbgPrintMachineInfo(TracePoint & aTP);
	void dbgCommandMachine();
	void dbgCommandMachines();

	void dbgCommandParametersMachine();

	void dbgPrintStateInfo(TracePoint & aTP);
	void dbgCommandState();
	void dbgCommandStates();

	void dbgPrintStatemachineInfo(TracePoint & aTP);
	void dbgCommandStatemachine();
	void dbgCommandStatemachines();

	void dbgPrintTransitionInfo(const TracePoint & aTP);
	void dbgCommandTransition();
	void dbgCommandTransitions();

	void dbgPrintRoutineInfo(const TracePoint & aTP);
	void dbgCommandRoutine();
	void dbgCommandRoutines();

	void dbgPrintRunnableInfo(const TracePoint & aTP);
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
