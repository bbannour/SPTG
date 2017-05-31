/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mars 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExtenderProcessorUnit.h"

#include <fam/api/MainProcessorUnit.h>

#include <fml/operator/OperatorManager.h>

#include <fml/trace/TraceFactory.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{


ExtenderProcessorUnit::ExtenderProcessorUnit(
		SymbexControllerUnitManager & aControllerUnitManager,
		WObject * wfParameterObject)
: RegisteredProcessorUnit( aControllerUnitManager , wfParameterObject ,
		AVM_PRE_PROCESSING_STAGE , PRECEDENCE_OF_EXTENDER_PROCESSOR),
mLocalExecutableForm( getConfiguration().getExecutableSystem() , 0 ),
mTraceObjective( OperatorManager::OPERATOR_OR ),
mTraceChecker( ENV, &mLocalExecutableForm )
{
	//!! NOTHING
}


/**
 * CONFIGURE
 */
bool ExtenderProcessorUnit::configureImpl()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
			<< "Unexpected NULL ExtenderProcessorUnit WObject !!!"
			<< SEND_EXIT;

	WObject * theTRACE = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("trace", "TRACE"));
	if( (theTRACE == WObject::_NULL_) || theTRACE->hasnoOwnedElement() )
	{
		return true;
	}

	// Configuration of TRACE
	TraceFactory traceFactory(getConfiguration(), ENV,
			getParameterWObject(), &mLocalExecutableForm);

	if( traceFactory.configure(& mTraceObjective) )
	{
//		return( false );
	}

	return( true );
}


/**
 * REPORT TRACE
 */
void ExtenderProcessorUnit::reportDefault(OutStream & os) const
{
	os << TAB << "EXECUTION CHAIN" << std::endl;
}


/**
 * POST PROCESS
 */
bool ExtenderProcessorUnit::preprocess()
{
	ListOfExecutionContext potentialInputEC;
	potentialInputEC.splice( getConfiguration().getInputContext() );

	ListOfExecutionContext::const_iterator it = potentialInputEC.begin();
	ListOfExecutionContext::const_iterator itEnd = potentialInputEC.end();
	for( ; it != itEnd ; ++it )
	{
		collectContext(getConfiguration().getInputContext(), *(*it));
	}

	return( true );
}


void ExtenderProcessorUnit::collectContext(
		ListOfExecutionContext & inputContext, ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
		ExecutionContext::child_iterator it = anEC.begin();
		ExecutionContext::child_iterator itEnd = anEC.end();
		for( ; it != itEnd ; ++it )
		{
			collectContext(inputContext, *(*it));
		}
	}
	// case of leaf EC
	else if( anEC.hasFlags() || anEC.hasInfo() )
	{
		if( MainProcessorUnit::cleanFlagsIfReexecutable(anEC) )
		{
			appendIfRequiredExtension(inputContext, anEC);
		}
	}
	else
	{
		appendIfRequiredExtension(inputContext, anEC);
	}
}


void ExtenderProcessorUnit::appendIfRequiredExtension(
		ListOfExecutionContext & inputContext, ExecutionContext & anEC)
{
	if( mTraceObjective.nonempty()
		&& mTraceChecker.isSat(anEC, mTraceObjective) )
	{
		anEC.getwFlags().addCoverageElementTrace();

// TODO Create Info using the AvmCode of the mTraceObjective
		anEC.addInfo(*this,
				mTraceObjective.singleton()
						? mTraceObjective.first()
						: mTraceObjective.first() );

		anEC.getwFlags().addObjectiveAchievedTrace();
	}
	else
	{
		inputContext.append(& anEC);
	}
}


}
