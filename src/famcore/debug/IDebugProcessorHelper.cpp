/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 30 avr. 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "IDebugProcessorHelper.h"

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

const ExecutionContext * IDebugProcessorHelper::searchContext(
		const ExecutionContext * anEC, std::uint32_t ctxID)
{
	if( anEC->getIdNumber() == ctxID )
	{
		return( anEC );
	}

	else// if( anEC->nonempty() && (anEC->getIdNumber() < ctxID) )
	{
		for( const auto & itChildEC : anEC->getChildContexts() )
		{
			anEC = searchContext(itChildEC, ctxID);
			if( anEC != nullptr )
			{
				return( anEC );
			}
		}
	}

	return( nullptr );
}


bool IDebugProcessorHelper::hasExecutionContextTag(
		const ExecutionContext & anEC, const std::string & strFlag)
{
	bool isMatch = false;

	if( strFlag.starts_with("INFO") )
	{
		isMatch = anEC.hasInfo();
	}

	if( strFlag.starts_with("DEADELOCK") )
	{
		isMatch = anEC.getFlags().isExecutionDeadlockTrace();
	}
	else if( strFlag.starts_with("LIVELOCK") )
	{
		isMatch = anEC.getFlags().isExecutionLivelockTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("TRIVIAL", "LOOP")) )
	{
		isMatch = anEC.getFlags().isExecutionTrivialLoopTrace();
	}
	else if( strFlag.starts_with("REDUNDANCY") )
	{
		isMatch = anEC.getFlags().isExecutionRedundancyTrace();
	}

	else if( REGEX_MATCH(strFlag, PREFIX_WID("STATEMENT", "EXIT")) )
	{
		isMatch = anEC.getFlags().isExecutionStatementExitTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("SYMBEX", "LIMIT")) )
	{
		isMatch = anEC.getFlags().isExecutionSymbexLimitationTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("FATAL", "ERROR")) )
	{
		isMatch = anEC.getFlags().isExecutionFatalErrorTrace();
	}

	else if( strFlag.starts_with("COVERAGE") )
	{
		isMatch = anEC.getFlags().hasCoverageElementTrace();
	}

	else if( REGEX_MATCH(strFlag, PREFIX_WID("OBJECTIVE", OR_WID2("PASS", "ACHIEVED"))) )
	{
		isMatch = anEC.getFlags().hasObjectiveAchievedTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("OBJECTIVE", "INCONCLUSIVE")) )
	{
		isMatch = anEC.getFlags().hasObjectiveInconclusiveTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("OBJECTIVE", "FAILED")) )
	{
		isMatch = anEC.getFlags().hasObjectiveFailedTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("OBJECTIVE", "ABORT")) )
	{
		isMatch = anEC.getFlags().hasObjectiveAbortedTrace();
	}
	else if( REGEX_MATCH(strFlag, PREFIX_WID("OBJECTIVE", "TIMEOUT")) )
	{
		isMatch = anEC.getFlags().hasObjectiveTimeoutTrace();
	}

	else if( REGEX_MATCH(strFlag, OR_WID2("OBJECTIVE", "VERDICT")) )
	{
		isMatch = anEC.getFlags().hasCoverageElementTrace();
	}

	else if( REGEX_MATCH(strFlag, OR_WID2("ANALYSIS", "TRACE")) )
	{
		isMatch = anEC.getFlags().hasAnalysisTrace();
	}

	return isMatch;
}


} /* namespace sep */
