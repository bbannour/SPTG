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
#ifndef SEW_SYMBEX_DISPATCHER_H_
#define SEW_SYMBEX_DISPATCHER_H_

#include <common/AvmPointer.h>
#include <common/RunnableElement.h>

#include <sew/SymbexController.h>
#include <sew/SymbexEventManager.h>
#include <sew/SymbexProcessor.h>
#include <sew/SymbexControllerRequestManager.h>




namespace sep
{


class AvmPrimitiveProcessor;

class ExecutionContext;

class SymbexControllerUnitManager;
class SymbexEngine;


class SymbexDispatcher :
		public RunnableElement,
		public IHandlerEventDestroyCtx
{

	AVM_DECLARE_UNCLONABLE_CLASS(SymbexDispatcher)


protected:
	/**
	 * ATTRIBUTES
	 */
	SymbexEngine & mSymbexEngine;

	SymbexControllerUnitManager & mControllerUnitManager;

	SymbexEventManager mSymbexEventManager;

	SymbexControllerRequestManager mSymbexControllerRequestManager;

	SymbexProcessor mSymbexProcessor;

	SymbexController mSymbexController;

	avm_uint32_t mNextEvalNumber;

	avm_uint32_t mGlobalGraphWidth;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexDispatcher(SymbexEngine & anEngine, WObject * wfParameterObject,
			SymbexControllerUnitManager & aControllerUnitManager)
	: RunnableElement( wfParameterObject ),
	mSymbexEngine( anEngine ),
	mControllerUnitManager( aControllerUnitManager ),

	mSymbexEventManager( ),

	mSymbexControllerRequestManager( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexProcessor( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexController ( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mNextEvalNumber( 0 ),
	mGlobalGraphWidth( 1 )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexDispatcher()
	{
		// Unregistration
		mSymbexEventManager.unregisterHandlerEventDestroyCtx(this);
	}


	/**
	 * CONFIGURE
	 */
	bool configure();


	/**
	 * REPORT TRACE
	 */
	inline virtual void report(OutStream & os) const
	{
		mSymbexProcessor.report(os);

		mSymbexController.report(os);
	}


	/**
	 * INIT - EXIT
	 */
	virtual bool initImpl();

	virtual bool exitImpl();


	/**
	 * PRE - POST PROCESS
	 */
	bool preprocess();

	bool postprocess();

	/**
	 * start
	 */
	void start();

	/**
	 * Has Work
	 */
	inline bool hasWork() const
	{
		return( mSymbexControllerRequestManager.hasRequestEnabled()
				|| mControllerUnitManager.hasWork() );
	}

	inline bool hasReadyWork() const
	{
		return( mSymbexControllerRequestManager.hasntRequestStop()
				&& mControllerUnitManager.hasReadyWork() );
	}


	/**
	 * Send an  ExecutionContext to
	 * Execution or Analyser working Queue
	 */
	inline void sendToExecutionWorkingQueue(ExecutionContext * anEC)
	{
		mSymbexProcessor.appendSymbexContext( anEC );
	}

	inline void sendToAnalyserWorkingQueue(ExecutionContext * anEC)
	{
		mSymbexController.appendSymbexContext( anEC );
	}


	/**
	 * GETTER - SETTER
	 * mSymbexEngine
	 */
	inline SymbexEngine & getSymbexEngine() const
	{
		return( mSymbexEngine );
	}

	/**
	 * GETTER
	 * AvmPrimitiveProcessor
	 */
	AvmPrimitiveProcessor & getPrimitiveProcessor() const;


	/**
	 * GETTER - SETTER
	 * mSymbexEventManager
	 */
	inline SymbexEventManager & getSymbexEventManager()
	{
		return( mSymbexEventManager );
	}


	/**
	 * GETTER - SETTER
	 * mSymbexControllerRequestManager
	 */
	inline 	SymbexControllerRequestManager & getSymbexControllerRequestManager()
	{
		return( mSymbexControllerRequestManager );
	}


	/**
	 * GETTER - SETTER
	 * mSymbexProcessor
	 */
	inline SymbexProcessor & getSymbexProcessor()
	{
		return( mSymbexProcessor );
	}

	inline ListOfExecutionContext & getExecutionWorkingQueue()
	{
		return( mSymbexProcessor.getSymbexContexts() );
	}


	/**
	 * GETTER - SETTER
	 * mSymbexController
	 */
	inline SymbexController & getSymbexController()
	{
		return( mSymbexController );
	}

	/**
	 * HANDLER for Event Notification
	 * Destroy Execution Context
	 */
	inline virtual void handleEventDestroyCtx(ExecutionContext * anEC)
	{
		mSymbexController.removeSymbexContext(anEC);

		mSymbexProcessor.removeSymbexContext(anEC);
	}


	/**
	 * GETTER - SETTER
	 * mNextEvalNumber
	 */
	inline avm_uint32_t getEvalNumber() const
	{
		return( mNextEvalNumber );
	}

	inline avm_uint32_t nextEvalNumber()
	{
		return( ++mNextEvalNumber );
	}


	/**
	 * GETTER - SETTER
	 * mGlobalGraphWidth
	 */
	inline avm_uint32_t getGlobalGraphWidth() const
	{
		return( mGlobalGraphWidth );
	}

	inline avm_uint32_t nextGlobalGraphWidth()
	{
		return( ++mGlobalGraphWidth );
	}


protected:
	/**
	 * report Eval
	 */
	inline void reportEval() const
	{
		mSymbexController.reportEval();
	}

};


} /* namespace sep */

#endif /*SEW_SYMBEX_DISPATCHER_H_*/
