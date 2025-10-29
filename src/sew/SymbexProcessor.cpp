/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SymbexProcessor.h"


#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/SymbexEngine.h>
#include <sew/SymbexDispatcher.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
SymbexProcessor::SymbexProcessor(
		SymbexDispatcher & aSymbexDispatcher, const WObject * wfParameterObject,
		SymbexControllerUnitManager & aControllerUnitManager)
: SymbexJob(aSymbexDispatcher, wfParameterObject, aControllerUnitManager),
mPrimitiveProcessor( aSymbexDispatcher.getPrimitiveProcessor() )
{
	//!! NOTHING
}


/**
 * CONFIGURE
 */
bool SymbexProcessor::configure()
{
	// INITIALIZATION
	mConfigFlag = SymbexJob::configure();


	return mConfigFlag;
}


/**
 * Thread main Run Method
 */
void SymbexProcessor::operator()()
{
	AVM_OS_TRACE << "Begin SymbexProcessor Thread" << std::endl;

	while( isLifecycleRunnable() )
	{
		runStep();
	}

	AVM_OS_TRACE << "End SymbexProcessor Thread" << std::endl;
}


/**
 * Execution <init> step
 */

void SymbexProcessor::initStep()
{
	RunnableElement::AutoRunningIdleSwitcher autoActivator( *this );

	traceBoundEval();

//	AVM_VERBOSITY_IF_HAS_MINIMUM
//		traceBoundEval();
//	AVM_VERBOSITY_ELSE
//		AVM_IF_DEBUG_ENABLED
//			traceBoundEval();
//		AVM_ENDIF_DEBUG_ENABLED
//	AVM_VERBOSITY_ENDIF

	while( hasSymbexContext() )
	{
		initStep( *( popFirstSymbexContext() ) );
	}
}

void SymbexProcessor::initStep(ExecutionContext & anEC)
{
	// STAT before PRINTING NEXT EVAL CONTEXT ID
	if( anEC.hasContainer()
		&& anEC.getContainer()->hasChildContext() )
	{
		// INVARIANT: the first child inherit their parent's width
		if( (anEC.getContainer()->firstChildContext() == (& anEC)) )
		{
			anEC.setWidth( anEC.getContainer()->getWidth() );
		}
		else
		{
			anEC.setWidth( mSymbexDispatcher.nextGlobalGraphWidth() );
		}
	}

	anEC.setEvalNumber( mSymbexDispatcher.nextEvalNumber() );

	// NEW EXECUTION PROCESSOR
	// Test necessaire en cas d'enchainement d'exécutions successives

	tracePreEval(anEC);

	if( anEC.hasContainer() )
	{
		mPrimitiveProcessor.run(anEC);
	}
	else
	{
		mPrimitiveProcessor.init(anEC);
	}

	tracePostEval(anEC);

	mSymbexDispatcher.sendToAnalyserWorkingQueue(& anEC);
}


/**
 * Execution <run> step
 */
void SymbexProcessor::runStep()
{
	RunnableElement::AutoRunningIdleSwitcher autoActivator( *this );

	while( hasSymbexContext() )
	{
		runStep( *( popFirstSymbexContext() ) );
	}
}



void SymbexProcessor::runStep(ExecutionContext & anEC)
{
	// STAT before PRINTING NEXT EVAL CONTEXT ID
	anEC.setEvalNumber( mSymbexDispatcher.nextEvalNumber() );

	tracePreEval(anEC);

	mPrimitiveProcessor.run(anEC);

	tracePostEval(anEC);

	mSymbexDispatcher.sendToAnalyserWorkingQueue(& anEC);
}


void SymbexProcessor::runStep(ExecutionContext & anEC, const BF & aRunnableElement)
{
	// STAT before PRINTING NEXT EVAL CONTEXT ID
	anEC.setEvalNumber( mSymbexDispatcher.nextEvalNumber() );

	tracePreEval(anEC);

	mPrimitiveProcessor.run(anEC, aRunnableElement);

	tracePostEval(anEC);

	mSymbexDispatcher.sendToAnalyserWorkingQueue(& anEC);
}


/**
 * EVAL TRACE
 */
void SymbexProcessor::traceBoundEval()
{
	if( AVM_ENABLED_SPIDER_VERBOSITY_FLAG )
	{
		mControllerUnitManager.traceInitSpider(AVM_OS_COUT);
	}

	mControllerUnitManager.traceBoundEval(AVM_OS_TRACE);

	mControllerUnitManager.traceBoundEval(AVM_OS_COUT);
}

void SymbexProcessor::tracePreEval(const ExecutionContext & anEC)
{
	if( AVM_ENABLED_SPIDER_VERBOSITY_FLAG )
	{
		mControllerUnitManager.traceStepSpider(AVM_OS_COUT, anEC);
	}

	mControllerUnitManager.tracePreEval(AVM_OS_TRACE, anEC);

	mControllerUnitManager.tracePreEval(AVM_OS_COUT, anEC);
}

void SymbexProcessor::tracePostEval(const ExecutionContext & anEC)
{
	mControllerUnitManager.tracePostEval(AVM_OS_TRACE, anEC);

	mControllerUnitManager.tracePostEval(AVM_OS_COUT, anEC);
}



}
