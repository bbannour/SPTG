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

#include "ExecutionContextFlags.h"

#include <sstream>

namespace sep
{

/**
 * Default Separator
 */
std::string ExecutionContextFlags::SEPARATOR = " & ";


/**
 * REACHED LIMIT to STRING
 */
std::string ExecutionContextFlags::strReachedLimit(
		bit_field_t reachedLimit, const std::string & separator)
{
	if( (reachedLimit != REACHED_UNDEFINED_LIMIT) )
	{
		std::ostringstream oss;

		oss << "REACHED-";

		if( (reachedLimit & REACHED_NODE_HEIGHT_LIMIT) != 0 )
		{
			oss << "NODE-HEIGHT-";
		}
		if( (reachedLimit & REACHED_NODE_WIDTH_LIMIT) != 0 )
		{
			oss << "NODE-WIDTH-";
		}
		if( (reachedLimit & REACHED_NODE_COUNT_LIMIT) != 0 )
		{
			oss << "NODE-COUNT-";
		}
		if( (reachedLimit & REACHED_SYMBEX_STEP_LIMIT) != 0 )
		{
			oss << "SYMBEX-STEP-";
		}

		oss << "LIMIT" << separator;

		return( oss.str() );
	}

	return( "" /*"<limit:unreached>"*/ );
}


/**
 * INTERRUPT REQUEST to STRING
 */
std::string ExecutionContextFlags::strInterruptRequest(
		bit_field_t interruptRequest, const std::string & separator)
{
	switch( interruptRequest )
	{
		case INTERRUPT_UNDEFINED_REQUEST:
			return( "" );
//			return( "<interrupt:undef>" + separator );

		case INTERRUPT_FAM_REQUEST:
			return( "FAM_IRQ" + separator );

		case INTERRUPT_USER_REQUEST:
			return( "USER_IRQ" + separator );

		default:
			return( "<interrupt:unknown>" + separator );
	}
}


/**
 * EXECUTION TRACE to STRING
 */
std::string ExecutionContextFlags::strExecutionTrace(
		bit_field_t executionTrace, const std::string & separator)
{
	switch( executionTrace )
	{
		case EXECUTION_UNDEFINED_TRACE:
			return( "" );
//			return( "<component:undef>" + separator );

		case EXECUTION_DEADLOCK_TRACE:
			return( "DEADLOCK" + separator );

		case EXECUTION_TRIVIAL_LOOP_TRACE:
			return( "TRIVIAL-LOOP" + separator );

		case EXECUTION_LIVELOCK_TRACE:
			return( "LIVELOCK" + separator );

		case EXECUTION_REDUNDANCY_TRACE:
			return( "REDUNDANCY-LEAF" + separator );

		case EXECUTION_REDUNDANCY_TARGET_TRACE:
			return( "REDUNDANCY-TARGET" + separator );

		case EXECUTION_STATEMENT_EXIT_TRACE:
			return( "STATEMENT-EXIT" + separator );

		case EXECUTION_FATAL_ERROR_TRACE:
			return( "FATAL-ERROR" + separator );

		case EXECUTION_SYMBEX_LIMIT_TRACE:
			return( "SYMBEX-LIMITATION" + separator );

		case EXECUTION_EXCEPTION_TRACE:
			return( "EXCEPTION" + separator );

		case EXECUTION_STEP_MARK_TRACE:
			return( "STEP-MARK" + separator );

		default:
			return( "<execution:unknown>" + separator );
	}
}


/**
 * ANALYSIS TRACE to STRING
 */
std::string ExecutionContextFlags::strAnalysisTrace(
		bit_field_t analysisTrace, const std::string & separator)
{
	if( analysisTrace != FAM_UNDEFINED_TRACE )
	{
		std::ostringstream oss;

		if( (analysisTrace & FAM_COVERAGE_ELEMENT_TRACE) != 0 )
		{
			oss << "COVERAGE-ELEMENT" << separator;
		}

		if( (analysisTrace & FAM_OBJECTIVE_ACHIEVED_TRACE) != 0 )
		{
			oss << "OBJECTIVE-ACHIEVED" << separator;
		}

		if( (analysisTrace & FAM_OBJECTIVE_FAILED_TRACE) != 0 )
		{
			oss << "OBJECTIVE-FAILED" << separator;
		}

		if( (analysisTrace & FAM_OBJECTIVE_ABORTED_TRACE) != 0 )
		{
			oss << "OBJECTIVE-ABORTED" << separator;
		}

		return( oss.str() );
	}

	return( "" );
//	return( "<analysis:undef>" + separator );
}




} /* namespace sep */
