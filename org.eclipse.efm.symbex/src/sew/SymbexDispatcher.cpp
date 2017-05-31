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
	mSymbexEventManager.registerHandlerEventDestroyCtx(this);

	return( true );
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

	mSymbexProcessor.initStep();

	mSymbexController.analyseResult();

	while( mSymbexController.isLifecycleRunnable() )
	{
		mSymbexController.analyseReady();

		mSymbexProcessor.runStep();

		mSymbexController.analyseResult();
	}

	// Last step-eval trace
	reportEval();
}


}
