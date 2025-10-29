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


#include <cstdint>

#include <util/avm_string.h>


namespace sep
{

struct ExecutionContextFlags
{

	/**
	 * REACHED_LIMIT
	 * 5 bits
	 */
	enum REACHED_LIMIT
	{
		REACHED_UNDEFINED_LIMIT          = 0x000,

		REACHED_NODE_HEIGHT_LIMIT        = 0x001,

		REACHED_NODE_WIDTH_LIMIT         = 0x002,

		REACHED_NODE_COUNT_LIMIT         = 0x004,

		REACHED_SYMBEX_EVAL_LIMIT        = 0x008,

		REACHED_SYMBEX_STEP_LIMIT        = 0x010,

	};

	/**
	 * INTERRUPT_REQUEST
	 * 1 bits
	 */
	enum INTERRUPT_REQUEST
	{
		INTERRUPT_UNDEFINED_REQUEST      = 0x00,

		INTERRUPT_USER_REQUEST           = 0x01,

//		INTERRUPT_FAM_REQUEST            = 0x02,

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
	 * FORMAL ANALYSIS MODULE as FAM_VERDICT
	 * 6 bits
	 */
	enum FAM_VERDICT
	{
		FAM_UNDEFINED_VERDICT              = 0x000,

		FAM_COVERAGE_ELEMENT_VERDICT       = 0x001,

		FAM_OBJECTIVE_ACHIEVED_VERDICT     = 0x002,

		FAM_OBJECTIVE_INCONCLUSIVE_VERDICT = 0x004,

		FAM_OBJECTIVE_FAILED_VERDICT       = 0x008,

		FAM_OBJECTIVE_ABORTED_VERDICT      = 0x010,

		FAM_OBJECTIVE_TIMEOUT_VERDICT      = 0x020,

		FAM_ANY_OBJECTIVE_VERDICT          = FAM_OBJECTIVE_ACHIEVED_VERDICT
		                                   | FAM_OBJECTIVE_INCONCLUSIVE_VERDICT
		                                   | FAM_OBJECTIVE_FAILED_VERDICT
		                                   | FAM_OBJECTIVE_ABORTED_VERDICT
		                                   | FAM_OBJECTIVE_TIMEOUT_VERDICT

	};



	/**
	 * TYPEDEF
	 */
	typedef std::uint16_t  bit_field_t;

	/**
	 * BIT FIELDS
	 */
	// group 1 : 16 bits
	bit_field_t limit          : 5;

	bit_field_t interrupt      : 1;

	bit_field_t execution      : 4;

	bit_field_t analysis       : 6;



	/**
	 * CONSTRUCTORS
	 */
	ExecutionContextFlags()
	: limit( REACHED_UNDEFINED_LIMIT ),
	interrupt( INTERRUPT_UNDEFINED_REQUEST ),
	execution( EXECUTION_UNDEFINED_TRACE ),
	analysis( FAM_UNDEFINED_VERDICT )
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
		return(    (limit     != REACHED_UNDEFINED_LIMIT    )
				|| (interrupt != INTERRUPT_UNDEFINED_REQUEST)
				|| (execution != EXECUTION_UNDEFINED_TRACE  )
				|| (analysis  != FAM_UNDEFINED_VERDICT      ) );
	}

	inline bool hasReachedLimitOrExecutionTrace() const
	{
		return(    (limit     != REACHED_UNDEFINED_LIMIT  )
				|| (execution != EXECUTION_UNDEFINED_TRACE) );
	}

	inline bool isUndefined() const
	{
		return(    (limit     == REACHED_UNDEFINED_LIMIT    )
				&& (interrupt == INTERRUPT_UNDEFINED_REQUEST)
				&& (execution == EXECUTION_UNDEFINED_TRACE  )
				&& (analysis == FAM_UNDEFINED_VERDICT       ) );
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
	inline bool isReachedSymbexEvalLimit() const
	{
		return( limit == REACHED_SYMBEX_EVAL_LIMIT );
	}

	inline bool hasReachedSymbexEvalLimit() const
	{
		return( (limit & REACHED_SYMBEX_EVAL_LIMIT) != 0 );
	}


	inline ExecutionContextFlags & addReachedSymbexEvalLimit()
	{
		limit |= REACHED_SYMBEX_EVAL_LIMIT;

		return( *this );
	}

	inline ExecutionContextFlags & setReachedSymbexEvalLimit()
	{
		limit = REACHED_SYMBEX_EVAL_LIMIT;

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
//	inline bool isInterruptModuleRequest() const
//	{
//		return( interrupt == INTERRUPT_FAM_REQUEST );
//	}
//
//	inline ExecutionContextFlags & setInterruptModuleRequest()
//	{
//		interrupt = INTERRUPT_FAM_REQUEST;
//
//		return( *this );
//	}

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
	inline FAM_VERDICT getAnalysisTrace() const
	{
		return( static_cast< FAM_VERDICT >( analysis ) );
	}

	inline bool hasAnalysisTrace() const
	{
		return( analysis != REACHED_UNDEFINED_LIMIT );
	}

	inline bool noneAnalysisTrace() const
	{
		return( analysis == REACHED_UNDEFINED_LIMIT );
	}

	inline bool hasAnalysisTrace(FAM_VERDICT analysisTrace) const
	{
		return( (analysis & analysisTrace) != 0 );
	}

	inline bool isAnalysisTrace(FAM_VERDICT analysisTrace) const
	{
		return( analysis == analysisTrace );
	}

	inline ExecutionContextFlags & setAnalysisTrace(FAM_VERDICT analysisTrace)
	{
		analysis = analysisTrace;

		return( *this );
	}

	inline ExecutionContextFlags & unsetAnalysisTrace()
	{
		analysis = FAM_UNDEFINED_VERDICT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "coverage" analysis
	 */
	inline bool hasCoverageElementTrace() const
	{
		return( (analysis & FAM_COVERAGE_ELEMENT_VERDICT) != 0 );
	}

	inline bool isCoverageElementTrace() const
	{
		return( analysis == FAM_COVERAGE_ELEMENT_VERDICT );
	}

	inline bool noneCoverageElementTrace() const
	{
		return( (analysis & FAM_COVERAGE_ELEMENT_VERDICT) == 0 );
	}

	inline ExecutionContextFlags & addCoverageElementTrace()
	{
		analysis |= FAM_COVERAGE_ELEMENT_VERDICT;

		return( *this );
	}

	inline ExecutionContextFlags & setCoverageElementTrace()
	{
		analysis = FAM_COVERAGE_ELEMENT_VERDICT;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "any objective" analysis
	 */
	inline bool hasAnyObjectiveVerdict() const
	{
		return( (analysis & FAM_ANY_OBJECTIVE_VERDICT) != 0 );
	}


	/**
	 * GETTER - SETTER
	 * "objective achieved" analysis
	 */
	inline bool hasObjectiveAchievedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ACHIEVED_VERDICT) != 0 );
	}

	inline bool isObjectiveAchievedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_ACHIEVED_VERDICT );
	}

	inline bool noneObjectiveAchievedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ACHIEVED_VERDICT) == 0 );
	}

	inline ExecutionContextFlags & setObjectiveAchievedTrace()
	{
		analysis |= FAM_OBJECTIVE_ACHIEVED_VERDICT;

		return( *this );
	}

	inline ExecutionContextFlags & unsetObjectiveAchievedTrace()
	{
		analysis = (analysis & (~ FAM_OBJECTIVE_ACHIEVED_VERDICT));

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "objective inconclusive" analysis
	 */
	inline bool hasObjectiveInconclusiveTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_INCONCLUSIVE_VERDICT) != 0 );
	}

	inline bool isObjectiveInconclusiveTrace() const
	{
		return( analysis == FAM_OBJECTIVE_INCONCLUSIVE_VERDICT );
	}

	inline ExecutionContextFlags & setObjectiveInconclusiveTrace()
	{
		analysis |= FAM_OBJECTIVE_INCONCLUSIVE_VERDICT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "objective failed" analysis
	 */
	inline bool hasObjectiveFailedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_FAILED_VERDICT) != 0 );
	}

	inline bool isObjectiveFailedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_FAILED_VERDICT );
	}


	inline ExecutionContextFlags & setObjectiveFailedTrace()
	{
		analysis |= FAM_OBJECTIVE_FAILED_VERDICT;

		return( *this );
	}

	/**
	 * GETTER - SETTER
	 * "objective aborted" analysis
	 */
	inline bool hasObjectiveAbortedTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_ABORTED_VERDICT) != 0 );
	}

	inline bool isObjectiveAbortedTrace() const
	{
		return( analysis == FAM_OBJECTIVE_ABORTED_VERDICT );
	}

	inline ExecutionContextFlags & setObjectiveAbortedTrace()
	{
		analysis |= FAM_OBJECTIVE_ABORTED_VERDICT;

		return( *this );
	}


	/**
	 * GETTER - SETTER
	 * "objective timeout" analysis
	 */
	inline bool hasObjectiveTimeoutTrace() const
	{
		return( (analysis & FAM_OBJECTIVE_TIMEOUT_VERDICT) != 0 );
	}

	inline bool isObjectiveTimeoutTrace() const
	{
		return( analysis == FAM_OBJECTIVE_TIMEOUT_VERDICT );
	}

	inline ExecutionContextFlags & setObjectiveTimeoutTrace()
	{
		analysis |= FAM_OBJECTIVE_TIMEOUT_VERDICT;

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

	inline bool hasObjectiveInconclusive() const
	{
		return( hasObjectiveInconclusiveTrace() );
	}

	inline bool hasObjectiveFailed() const
	{
		return( hasObjectiveFailedTrace() );
	}

	inline bool hasObjectiveAborted() const
	{
		return( hasObjectiveAbortedTrace() );
	}

	inline bool hasObjectiveTimeout() const
	{
		return( hasObjectiveTimeoutTrace() );
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
	 * ANALYSIS VERDICT to STRING
	 */
	inline std::string strAnalysisVerdict(
			const std::string & separator = " ") const
	{
		return( ExecutionContextFlags::strAnalysisVerdict(
				analysis , separator ) );
	}

	static std::string strAnalysisVerdict(bit_field_t analysisTrace,
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
				ExecutionContextFlags::strAnalysisVerdict(
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
