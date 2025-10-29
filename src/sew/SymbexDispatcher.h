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

#include <common/RunnableElement.h>

#include <sew/SymbexController.h>
#include <sew/SymbexControllerEventManager.h>
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

	SymbexControllerEventManager mSymbexControllerEventManager;

	SymbexControllerRequestManager mSymbexControllerRequestManager;

	SymbexProcessor mSymbexProcessor;

	SymbexController mSymbexController;

	std::uint32_t mSymbexStepCount;

	std::uint32_t mNextEvalNumber;

	std::uint32_t mGlobalGraphWidth;

	ListOfExecutionContext mLastEvalContexts;
	ListOfExecutionContext mLastResultContexts;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexDispatcher(SymbexEngine & anEngine, const WObject * wfParameterObject,
			SymbexControllerUnitManager & aControllerUnitManager)
	: RunnableElement( wfParameterObject ),
	mSymbexEngine( anEngine ),
	mControllerUnitManager( aControllerUnitManager ),

	mSymbexControllerEventManager( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexControllerRequestManager( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexProcessor( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexController( (*this) ,
			wfParameterObject , aControllerUnitManager ),

	mSymbexStepCount( 0 ),
	mNextEvalNumber ( 0 ),

	mGlobalGraphWidth( 1 ),

	mLastEvalContexts( ),
	mLastResultContexts( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexDispatcher()
	{
		// Unregistration
		mSymbexControllerEventManager.unregisterHandlerEventDestroyCtx(this);
	}


	/**
	 * CONFIGURE
	 */
	bool configure() override;


	/**
	 * REPORT TRACE
	 */
	inline virtual void report(OutStream & os) const override
	{
		mSymbexProcessor.report(os);

		mSymbexController.report(os);
	}

	// Due to [-Woverloaded-virtual=]
	using RunnableElement::report;


	/**
	 * INIT - EXIT
	 */
	virtual bool initImpl() override;

	virtual bool exitImpl() override;


	/**
	 * PRE - POST PROCESS
	 */
	virtual bool preprocess() override;

	virtual bool postprocess() override;

	/**
	 * start
	 */
	void start();

	void initStep();

	void runStep();

	void runStep(ExecutionContext & anEC);

	void runStep(ExecutionContext & anEC, const BF & aRunnableElement);

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
		return( mSymbexControllerRequestManager.hasnoRequestStop()
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
	 * mSymbexControllerEventManager
	 */
	inline SymbexControllerEventManager & getSymbexEventManager()
	{
		return( mSymbexControllerEventManager );
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
	inline virtual void handleEventDestroyCtx(ExecutionContext * anEC) override
	{
		mSymbexController.removeSymbexContext(anEC);

		mSymbexProcessor.removeSymbexContext(anEC);
	}


	/**
	 * GETTER - SETTER
	 * mSymbexStepCount
	 */
	inline std::uint32_t getSymbexStepCount() const
	{
		return( mSymbexStepCount );
	}

	inline void incrSymbexStepCount()
	{
		++mSymbexStepCount;
	}


	/**
	 * GETTER - SETTER
	 * mNextEvalNumber
	 */
	inline std::uint32_t getEvalNumber() const
	{
		return( mNextEvalNumber );
	}

	inline std::uint32_t nextEvalNumber()
	{
		return( ++mNextEvalNumber );
	}


	/**
	 * GETTER - SETTER
	 * mGlobalGraphWidth
	 */
	inline std::uint32_t getGlobalGraphWidth() const
	{
		return( mGlobalGraphWidth );
	}

	inline std::uint32_t nextGlobalGraphWidth()
	{
		return( ++mGlobalGraphWidth );
	}


	/**
	 * GETTER - SETTER
	 * mLastEvalContexts
	 * mLastResultContexts
	 */
	inline ListOfExecutionContext & getLastEvalContexts()
	{
		return( mLastEvalContexts );
	}

	inline ListOfExecutionContext & getLastResultContexts()
	{
		return( mLastResultContexts );
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
