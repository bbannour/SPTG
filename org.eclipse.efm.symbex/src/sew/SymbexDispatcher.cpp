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

#include "SymbexDispatcher.h"

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/WObject.h>

#include <sew/SymbexEngine.h>


namespace sep
{


/**
 * GETTER
 * AvmPrimitiveProcessor
 */
AvmPrimitiveProcessor & SymbexDispatcher::getPrimitiveProcessor() const
{
	return( mSymbexEngine.getPrimitiveProcessor() );
}


/**
 * CONFIGURE
 */
bool SymbexDispatcher::configure()
{
	mConfigFlag = RunnableElement::configure();

	if( not mSymbexProcessor.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexDispatcher::SymbexProcessor: configure failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	if( not mSymbexController.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexDispatcher::SymbexController: configure failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	// Registration to handler DestroyCtx event
	mSymbexControllerEventManager.registerHandlerEventDestroyCtx(this);

	return( mConfigFlag );
}


/**
 * INIT
 */
bool SymbexDispatcher::initImpl()
{
	bool isEC_OK = mSymbexProcessor.init();

	bool isAC_OK = mSymbexController.init();

	return( isEC_OK && isAC_OK );
}

/**
 * EXIT
 */
bool  SymbexDispatcher::exitImpl()
{
	bool isEC_OK = mSymbexProcessor.exit();

	bool isAC_OK = mSymbexController.exit();

	return( isEC_OK && isAC_OK );
}


/**
 * PRE PROCESS
 */
bool  SymbexDispatcher::preprocess()
{
	bool isEC_OK = mSymbexProcessor.preprocess();

	bool isAC_OK = mSymbexController.preprocess();

	return( isEC_OK && isAC_OK );
}


/**
 * POST PROCESS
 */
bool  SymbexDispatcher::postprocess()
{
	bool isEC_OK = mSymbexProcessor.postprocess();

	bool isAC_OK = mSymbexController.postprocess();

	return( isEC_OK && isAC_OK );
}


/**
 * start
 */
void SymbexDispatcher::start()
{
	mSymbexProcessor.setLifecycleStarted();
	mSymbexController.setLifecycleStarted();

	mSymbexController.analyseReady();

	incrSymbexStepCount();
	mSymbexProcessor.initStep();

	mSymbexController.analyseResult();

	while( mSymbexController.isLifecycleRunnable() )
	{
		mSymbexController.analyseReady();

		incrSymbexStepCount();
		mSymbexProcessor.runStep();

		mSymbexController.analyseResult();
	}

	// Last step-eval trace
	reportEval();
}



void SymbexDispatcher::initStep()
{
	mSymbexProcessor.setLifecycleStarted();
	mSymbexController.setLifecycleStarted();

	mSymbexController.analyseReady();

	incrSymbexStepCount();

	mLastEvalContexts.clear();
	mLastEvalContexts.append( mSymbexProcessor.getSymbexContexts() );

	mSymbexProcessor.initStep();

	mLastResultContexts.clear();
	mLastResultContexts.append( mSymbexController.getSymbexContexts() );

	mSymbexController.analyseResult();
}

void SymbexDispatcher::runStep()
{
	mSymbexProcessor.setLifecycleStarted();
	mSymbexController.setLifecycleStarted();

	mSymbexController.analyseReady();

	incrSymbexStepCount();

	mLastEvalContexts.clear();
	mLastEvalContexts.append( mSymbexProcessor.getSymbexContexts() );

	mSymbexProcessor.runStep();

	mLastResultContexts.clear();
	mLastResultContexts.append( mSymbexController.getSymbexContexts() );

	mSymbexController.analyseResult();
}


void SymbexDispatcher::runStep(ExecutionContext & anEC)
{
	mSymbexProcessor.setLifecycleStarted();
	mSymbexController.setLifecycleStarted();

//	mSymbexController.analyseReady();
	getExecutionWorkingQueue().append(& anEC);

	incrSymbexStepCount();

	mLastEvalContexts.clear();
	mLastEvalContexts.append( mSymbexProcessor.getSymbexContexts() );

	mSymbexProcessor.runStep();

	mLastResultContexts.clear();
	mLastResultContexts.append( mSymbexController.getSymbexContexts() );

	mSymbexController.analyseResult();
}

void SymbexDispatcher::runStep(ExecutionContext & anEC, const BF & aRunnableElement)
{
	mSymbexProcessor.runStep(anEC, aRunnableElement);
}


}
