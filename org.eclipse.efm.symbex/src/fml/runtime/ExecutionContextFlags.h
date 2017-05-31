/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_RUNTIME_EXECUTIONCONTEXTFLAGS_H_
#define FML_RUNTIME_EXECUTIONCONTEXTFLAGS_H_

#include <util/avm_string.h>


namespace sep
{

struct ExecutionContextFlags
{

	/**
	 * REACHED_LIMIT
	 * 4 bits
	 */
	enum REACHED_LIMIT
	{
		REACHED_UNDEFINED_LIMIT          = 0x00,

		REACHED_NODE_HEIGHT_LIMIT        = 0x01,

		REACHED_NODE_WIDTH_LIMIT         = 0x02,

		REACHED_NODE_COUNT_LIMIT         = 0x04,

		REACHED_SYMBEX_STEP_LIMIT        = 0x08,

	};

	/**
	 * INTERRUPT_REQUEST
	 * 2 bits
	 */
	enum INTERRUPT_REQUEST
	{
		INTERRUPT_UNDEFINED_REQUEST      = 0x00,

		INTERRUPT_FAM_REQUEST            = 0x01,

		INTERRUPT_USER_REQUEST           = 0x02,

	};

	/**
	 * EXECUTION_TRACE
	 * 4 bits
	 */
	enum EXECUTION_TRACE
	{
		EXECUTION_UNDEFINED_TRACE         = 0x00,

		EXECUTION_DEADLOCK_TRACE          = 0x01,

		EXECUTION_TRIVIAL_LOOP_TRACE      = 0x02,

		EXECUTION_LIVELOCK_TRACE          = 0x03,

		EXECUTION_REDUNDANCY_TRACE        = 0x04,

		EXECUTION_REDUNDANCY_TARGET_TRACE = 0x05,

		EXECUTION_STATEMENT_EXIT_TRACE    = 0x06,

		EXECUTION_FATAL_ERROR_TRACE       = 0x07,

		EXECUTION_SYMBEX_LIMIT_TRACE      = 0x08,

		EXECUTION_EXCEPTION_TRACE         = 0x09,

		EXECUTION_STEP_MARK_TRACE         = 0x0A

	};

	/**
	 * FORMAL ANALYSIS MODULE as FAM_TRACE
	 * 3 bits
	 */
	enum FAM_TRACE
	{
		FAM_UNDEFINED_TRACE              = 0x00,

		FAM_COVERAGE_ELEMENT_TRACE       = 0x01,

		FAM_OBJECTIVE_ACHIEVED_TRACE     = 0x02,

		FAM_OBJECTIVE_FAILED_TRACE       = 0x04,

		FAM_OBJECTIVE_ABORTED_TRACE      = 0x08,

	};



	/**
	 * TYPEDEF
	 */
	typedef unsigned short  bit_field_t;

	/**
	 * BIT FIELDS
	 */
	bit_field_t limit          : 4;

	bit_field_t interrupt      : 2;

	bit_field_t execution      : 4;

	bit_field_t analysis       : 4;



	/**
	 * CONSTRUCTORS
	 */
	ExecutionContextFlags()
	: limit( REACHED_UNDEFINED_LIMIT ),
	interrupt( INTERRUPT_UNDEFINED_REQUEST ),
	execution( EXECUTION_UNDEFINED_TRACE ),
	analysis( FAM_UNDEFINED_TRACE )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~ExecutionContextFlags()
	{
		//!! NOTHING
	}



	/**
	 * TESTER - SETTER
	 */
	inline bool isDefined() const
	{
		return(    (limit     != REACHED_UNDEFINED_LIMIT  )
				|| (interrupt != EXECUTION_UNDEFINED_TRACE)
				|| (execution != EXECUTION_UNDEFINED_TRACE)
				|| (analysis != EXECUTION_UNDEFINED_TRACE ) );
	}

	inline bool hasReachedLimitOrExecutionTrace() const
	{
		return(    (limit     != REACHED_UNDEFINED_LIMIT  )
				|| (execution != EXECUTION_UNDEFINED_TRACE) );
	}

	inline bool isUndefined() const
	{
		return(    (limit     == REACHED_UNDEFINED_LIMIT  )
				&& (interrupt == EXECUTION_UNDEFINED_TRACE)
				&& (execution == EXECUTION_UNDEFINED_TRACE)
				&& (analysis == EXECUTION_UNDEFINED_TRACE ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// REACHED LIMIT
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * limit
	 */
	inline REACHED_LIMIT getReachedLimit() const
	{
		return( static_cast< REACHED_LIMIT >( limit ) );
	}

	inline bool hasReachedLimit() const
	{
		return( limit != REACHED_UNDEFINED_LIMIT );
	}

	inline bool noneReachedLimit() const
	{
		return( limit == REACHED_UNDEFINED_LIMIT );
	}

	inline bool isReachedLimit(REACHED_LIMIT reachedLimit) const
	{
		return( limit == reachedLimit );
	}

	inline ExecutionContextFlags & addReachedLimit(REACHED_LIMIT reachedLimit)
	{
		limit |= reachedLimit;

		return( *this );
	}

	inline ExecutionContextFlags & remReachedLimit(REACHED_LIMIT reachedLimit)
	{
		limit &= (~ reachedLimit);

		return( *this );
	}

	inline ExecutionContextFlags & setReachedLimit(REACHED_LIMIT reachedLimit)
	{
		limit = reachedLimit;

		return( *this );
	}

	inline ExecutionContextFlags & unsetReachedLimit()
	{
		limit = REACHED_UNDEFINED_LIMIT;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "node height" limit
	 */
	inline bool isReachedNodeHeightLimit() const
	{
		return( limit == REACHED_NODE_HEIGHT_LIMIT );
	}

	inline bool hasReachedNodeHeightLimit() const
	{
		return( (limit & REACHED_NODE_HEIGHT_LIMIT) != 0 );
	}

	inline ExecutionContextFlags & addReachedNodeHeightLimit()
	{
		limit |= REACHED_NODE_HEIGHT_LIMIT;

		return( *this );
	}

	inline ExecutionContextFlags & setReachedNodeHeightLimit()
	{
		limit = REACHED_NODE_HEIGHT_LIMIT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "node width" limit
	 */
	inline bool isReachedNodeWidthLimit() const
	{
		return( limit == REACHED_NODE_WIDTH_LIMIT );
	}

	inline bool hasReachedNodeWidthLimit() const
	{
		return( (limit & REACHED_NODE_WIDTH_LIMIT) != 0 );
	}

	inline ExecutionContextFlags & addReachedNodeWidthLimit()
	{
		limit |= REACHED_NODE_WIDTH_LIMIT;

		return( *this );
	}

	inline ExecutionContextFlags & setReachedNodeWidthLimit()
	{
		limit = REACHED_NODE_WIDTH_LIMIT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "node count" limit
	 */
	inline bool isReachedNodeCountLimit() const
	{
		return( limit == REACHED_NODE_COUNT_LIMIT );
	}

	inline bool hasReachedNodeCountLimit() const
	{
		return( (limit & REACHED_NODE_COUNT_LIMIT) != 0 );
	}

	inline ExecutionContextFlags & addReachedNodeCountLimit()
	{
		limit |= REACHED_NODE_COUNT_LIMIT;

		return( *this );
	}

	inline ExecutionContextFlags & setReachedNodeCountLimit()
	{
		limit = REACHED_NODE_COUNT_LIMIT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "execution step" limit
	 */
	inline bool isReachedSymbexStepLimit() const
	{
		return( limit == REACHED_SYMBEX_STEP_LIMIT );
	}

	inline bool hasReachedSymbexStepLimit() const
	{
		return( (limit & REACHED_SYMBEX_STEP_LIMIT) != 0 );
	}


	inline ExecutionContextFlags & addReachedSymbexStepLimit()
	{
		limit |= REACHED_SYMBEX_STEP_LIMIT;

		return( *this );
	}

	inline ExecutionContextFlags & setReachedSymbexStepLimit()
	{
		limit = REACHED_SYMBEX_STEP_LIMIT;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// REACHED LIMIT
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * interrupt
	 */
	inline INTERRUPT_REQUEST getInterruptRequest() const
	{
		return( static_cast< INTERRUPT_REQUEST >( interrupt ) );
	}

	inline bool hasInterruptRequest() const
	{
		return( interrupt != REACHED_UNDEFINED_LIMIT );
	}

	inline bool noneInterruptRequest() const
	{
		return( interrupt == REACHED_UNDEFINED_LIMIT );
	}

	inline bool isInterruptRequest(INTERRUPT_REQUEST interruptRequest) const
	{
		return( interrupt == interruptRequest );
	}

	inline ExecutionContextFlags & setInterruptRequest(
			INTERRUPT_REQUEST interruptRequest)
	{
		interrupt = interruptRequest;

		return( *this );
	}

	inline ExecutionContextFlags & unsetInterruptRequest()
	{
		interrupt = REACHED_UNDEFINED_LIMIT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "formal analysis module" as "fam" request
	 */
	inline bool isInterruptModuleRequest() const
	{
		return( interrupt == INTERRUPT_FAM_REQUEST );
	}

	inline ExecutionContextFlags & setInterruptModuleRequest()
	{
		interrupt = INTERRUPT_FAM_REQUEST;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "fam" request
	 */
	inline bool isInterruptUserRequest() const
	{
		return( interrupt == INTERRUPT_USER_REQUEST );
	}

	inline ExecutionContextFlags & setInterruptUserRequest()
	{
		interrupt = INTERRUPT_USER_REQUEST;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// EXECUTION TRACE
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * execution
	 */
	inline EXECUTION_TRACE getExecutionTrace() const
	{
		return( static_cast< EXECUTION_TRACE >( execution ) );
	}

	inline bool hasExecutionTrace() const
	{
		return( execution != EXECUTION_UNDEFINED_TRACE );
	}

	inline bool noneExecutionTrace() const
	{
		return( execution == EXECUTION_UNDEFINED_TRACE );
	}

	inline bool isExecutionTrace(EXECUTION_TRACE reachedLimit) const
	{
		return( execution == reachedLimit );
	}

	inline ExecutionContextFlags & addExecutionTrace(EXECUTION_TRACE reachedLimit)
	{
		execution |= reachedLimit;

		return( *this );
	}

	inline ExecutionContextFlags & remExecutionTrace(EXECUTION_TRACE reachedLimit)
	{
		execution &= (~ reachedLimit);

		return( *this );
	}

	inline ExecutionContextFlags & setExecutionTrace(EXECUTION_TRACE reachedLimit)
	{
		execution = reachedLimit;

		return( *this );
	}

	inline ExecutionContextFlags & unsetExecutionTrace()
	{
		execution = EXECUTION_UNDEFINED_TRACE;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "deadlock" execution
	 */
	inline bool isExecutionDeadlockTrace() const
	{
		return( execution == EXECUTION_DEADLOCK_TRACE );
	}

	inline ExecutionContextFlags & setExecutionDeadlockTrace()
	{
		execution = EXECUTION_DEADLOCK_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "trivial_loop" execution
	 */
	inline bool isExecutionTrivialLoopTrace() const
	{
		return( execution == EXECUTION_TRIVIAL_LOOP_TRACE );
	}

	inline ExecutionContextFlags & setExecutionTrivialLoopTrace()
	{
		execution = EXECUTION_TRIVIAL_LOOP_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "livelock" execution
	 */
	inline bool isExecutionLivelockTrace() const
	{
		return( execution == EXECUTION_LIVELOCK_TRACE );
	}

	inline ExecutionContextFlags & setExecutionLivelockTrace()
	{
		execution = EXECUTION_LIVELOCK_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "redundancy" execution
	 */
	inline bool isExecutionRedundancyTrace() const
	{
		return( execution == EXECUTION_REDUNDANCY_TRACE );
	}

	inline ExecutionContextFlags & setExecutionRedundancyTrace()
	{
		execution = EXECUTION_REDUNDANCY_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "redundancy target" execution
	 */
	inline bool isExecutionRedundancyTargetTrace() const
	{
		return( execution == EXECUTION_REDUNDANCY_TARGET_TRACE );
	}

	inline bool noneExecutionRedundancyTargetTrace() const
	{
		return( execution != EXECUTION_REDUNDANCY_TARGET_TRACE );
	}

	inline ExecutionContextFlags & setExecutionRedundancyTargetTrace()
	{
		execution = EXECUTION_REDUNDANCY_TARGET_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "statement_exit" execution
	 */
	inline bool isExecutionStatementExitTrace() const
	{
		return( execution == EXECUTION_STATEMENT_EXIT_TRACE );
	}

	inline ExecutionContextFlags & setExecutionStatementExitTrace()
	{
		execution = EXECUTION_STATEMENT_EXIT_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "fatal_error" execution
	 */
	inline bool isExecutionFatalErrorTrace() const
	{
		return( execution == EXECUTION_FATAL_ERROR_TRACE );
	}

	inline ExecutionContextFlags & setExecutionFatalErrorTrace()
	{
		execution = EXECUTION_FATAL_ERROR_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "boundary" execution
	 */
	inline bool isExecutionSymbexLimitationTrace() const
	{
		return( execution == EXECUTION_SYMBEX_LIMIT_TRACE );
	}

	inline ExecutionContextFlags & setExecutionSymbexLimitationTrace()
	{
		execution = EXECUTION_SYMBEX_LIMIT_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "exception" execution
	 */
	inline bool isExecutionExceptionTrace() const
	{
		return( execution == EXECUTION_EXCEPTION_TRACE );
	}

	inline ExecutionContextFlags & setExecutionExceptionTrace()
	{
		execution = EXECUTION_EXCEPTION_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "step_mark" execution
	 */
	inline bool isExecutionStepMarkTrace() const
	{
		return( execution == EXECUTION_STEP_MARK_TRACE );
	}

	inline ExecutionContextFlags & setExecutionStepMarkTrace()
	{
		execution = EXECUTION_STEP_MARK_TRACE;

		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	// ANALYSIS TRACE
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * analysis
	 */
	inline FAM_TRACE getAnalysisTrace() const
	{
		return( static_cast< FAM_TRACE >( analysis ) );
	}

	inline bool hasAnalysisTrace() const
	{
		return( analysis != REACHED_UNDEFINED_LIMIT );
	}

	inline bool noneAnalysisTrace() const
	{
		return( analysis == REACHED_UNDEFINED_LIMIT );
	}

	inline bool hasAnalysisTrace(FAM_TRACE analysisTrace) const
	{
		return( (analysis & analysisTrace) != 0 );
	}

	inline bool isAnalysisTrace(FAM_TRACE analysisTrace) const
	{
		return( analysis == analysisTrace );
	}

	inline ExecutionContextFlags & setAnalysisTrace(FAM_TRACE analysisTrace)
	{
		analysis = analysisTrace;

		return( *this );
	}

	inline ExecutionContextFlags & unsetAnalysisTrace()
	{
		analysis = FAM_UNDEFINED_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "coverage" analysis
	 */
	inline bool hasCoverageElementTrace() const
	{
		return( (analysis & FAM_COVERAGE_ELEMENT_TRACE) != 0 );
	}

	inline bool isCoverageElementTrace() const
	{
		return( analysis == FAM_COVERAGE_ELEMENT_TRACE );
	}

	inline bool noneCoverageElementTrace() const
	{
		return( (analysis & FAM_COVERAGE_ELEMENT_TRACE) == 0 );
	}

	inline ExecutionContextFlags & addCoverageElementTrace()
	{
		analysis |= FAM_COVERAGE_ELEMENT_TRACE;

		return( *this );
	}

	inline ExecutionContextFlags & setCoverageElementTrace()
	{
		analysis = FAM_COVERAGE_ELEMENT_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "coverage" analysis
	 */
	inline bool hasObjectiveAchievedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ACHIEVED_TRACE) != 0 );
	}

	inline bool isObjectiveAchievedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_ACHIEVED_TRACE );
	}

	inline bool noneObjectiveAchievedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ACHIEVED_TRACE) == 0 );
	}

	inline ExecutionContextFlags & addObjectiveAchievedTrace()
	{
		analysis |= FAM_OBJECTIVE_ACHIEVED_TRACE;

		return( *this );
	}

	inline ExecutionContextFlags & setObjectiveAchievedTrace()
	{
		analysis = FAM_OBJECTIVE_ACHIEVED_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "coverage" analysis
	 */
	inline bool hasObjectiveFailedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_FAILED_TRACE) != 0 );
	}

	inline bool isObjectiveFailedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_FAILED_TRACE );
	}

	inline ExecutionContextFlags & addObjectiveFailedTrace()
	{
		analysis |= FAM_OBJECTIVE_FAILED_TRACE;

		return( *this );
	}

	inline ExecutionContextFlags & setObjectiveFailedTrace()
	{
		analysis = FAM_OBJECTIVE_FAILED_TRACE;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "coverage" analysis
	 */
	inline bool hasObjectiveAbortedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ABORTED_TRACE) != 0 );
	}

	inline bool isObjectiveAbortedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_ABORTED_TRACE );
	}

	inline ExecutionContextFlags & addObjectiveAbortedTrace()
	{
		analysis |= FAM_OBJECTIVE_ABORTED_TRACE;

		return( *this );
	}

	inline ExecutionContextFlags & setObjectiveAbortedTrace()
	{
		analysis = FAM_OBJECTIVE_ABORTED_TRACE;

		return( *this );
	}


	/**
	 * REEXECUTABILITY
	 */
	inline bool isReexecutable() const
	{
		return( noneExecutionTrace() );
	}

	inline ExecutionContextFlags & setReexecutable()
	{
		limit = REACHED_UNDEFINED_LIMIT;

		interrupt = INTERRUPT_UNDEFINED_REQUEST;

		return( *this );
	}


	/**
	 * CATEGORY TEST
	 */
	inline bool hasError() const
	{
		return( isExecutionFatalErrorTrace()
				|| isExecutionSymbexLimitationTrace() );
	}

	inline bool hasAlert() const
	{
		return( isExecutionDeadlockTrace()
				|| isExecutionLivelockTrace()
				|| isExecutionStatementExitTrace() );
	}

	inline bool hasWarning() const
	{
		return( hasReachedLimit() );
	}

	inline bool hasCoverageElement() const
	{
		return( hasCoverageElementTrace() );
	}

	inline bool hasObjectiveAchieved() const
	{
		return( hasObjectiveAchievedTrace() );
	}

	inline bool hasObjectiveFailed() const
	{
		return( hasObjectiveFailedTrace() );
	}

	inline bool hasObjectiveAborted() const
	{
		return( hasObjectiveAbortedTrace() );
	}

	inline bool hasRedundancy() const
	{
		return( isExecutionTrivialLoopTrace()
				|| isExecutionRedundancyTrace() );
	}

	inline bool hasRedundancyTarget() const
	{
		return( isExecutionRedundancyTargetTrace() );
	}


	/**
	 * Default Separator
	 */
	static std::string SEPARATOR;

	/**
	 * REACHED LIMIT to STRING
	 */
	inline std::string strReachedLimit(
			const std::string & separator = " & ") const
	{
		return( ExecutionContextFlags::strReachedLimit(
				limit , separator ) );
	}

	static std::string strReachedLimit(bit_field_t reachedLimit,
			const std::string & separator = SEPARATOR);

	/**
	 * INTERRUPT REQUEST to STRING
	 */
	inline std::string strInterruptRequest(
			const std::string & separator = " & ") const
	{
		return( ExecutionContextFlags::strInterruptRequest(
				interrupt , separator ) );
	}

	static std::string strInterruptRequest(bit_field_t interruptRequest,
			const std::string & separator = SEPARATOR);


	/**
	 * EXECUTION TRACE to STRING
	 */
	inline std::string strExecutionTrace(
			const std::string & separator = " ") const
	{
		return( ExecutionContextFlags::strExecutionTrace(
				execution , separator ) );
	}

	static std::string strExecutionTrace(bit_field_t executionTrace,
			const std::string & separator = SEPARATOR);

	/**
	 * ANALYSIS TRACE to STRING
	 */
	inline std::string strAnalysisTrace(
			const std::string & separator = " ") const
	{
		return( ExecutionContextFlags::strAnalysisTrace(
				analysis , separator ) );
	}

	static std::string strAnalysisTrace(bit_field_t analysisTrace,
			const std::string & separator = SEPARATOR);

	/**
	 * Serialization
	 */
	inline std::string str(const std::string & separator = SEPARATOR) const
	{
		return( StringTools::removeLastIfEndsWith(
				toString( separator ), separator) );
	}

	inline std::string toString(
			const std::string & separator = SEPARATOR) const
	{
		return( ExecutionContextFlags::strReachedLimit(
						limit , separator ) +
				ExecutionContextFlags::strInterruptRequest(
						interrupt , separator ) +
				ExecutionContextFlags::strExecutionTrace(
						execution , separator ) +
				ExecutionContextFlags::strAnalysisTrace(
						analysis , separator ) );
	}


};


class ExecutionContextFlagsImpl
{

protected:
	/**
	 * ATTRIBUTES
	 */
	ExecutionContextFlags mFlags;


public:
	/**
	 * CONSTRUCTOR
	 */
	ExecutionContextFlagsImpl()
	: mFlags( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	~ExecutionContextFlagsImpl()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 * mFlags
	 */
	inline const ExecutionContextFlags & getFlags() const
	{
		return( mFlags );
	}

	inline ExecutionContextFlags & getwFlags()
	{
		return( mFlags );
	}

	inline bool hasFlags() const
	{
		return( mFlags.isDefined() );
	}

	inline void setFlags(const ExecutionContextFlags & flags)
	{
		mFlags = flags;
	}

};


} /* namespace sep */

#endif /* FML_RUNTIME_EXECUTIONCONTEXTFLAGS_H_ */
