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
#ifndef SEW_SYMBEXJOB_H_
#define SEW_SYMBEXJOB_H_

#include <common/RunnableElement.h>
#include <collection/Typedef.h>
#include <fml/runtime/ExecutionContext.h>


namespace sep
{


class ExecutionContext;
class SymbexControllerUnitManager;
class SymbexDispatcher;


class SymbexJob :
		public RunnableElement
{


protected:
	/**
	 * TYPEDEF
	 */
	typedef List < ExecutionContext * >  ListOfExecutionContext;


protected:
	/**
	* ATTRIBUTES
	*/
	SymbexDispatcher & mSymbexDispatcher;

	SymbexControllerUnitManager & mControllerUnitManager;

	ListOfExecutionContext mSymbexContexts;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexJob(SymbexDispatcher & aSymbexDispatcher,
			WObject * wfParameterObject,
			SymbexControllerUnitManager & aCentralControllerUnit)
	: RunnableElement( wfParameterObject ),
	mSymbexDispatcher( aSymbexDispatcher ),
	mControllerUnitManager( aCentralControllerUnit ),
	mSymbexContexts( )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexJob()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl()
	{
		//!! NOTHING
		return true;
	}

	virtual bool exitImpl()
	{
		//!! NOTHING
		return true;
	}


	/**
	 * Thread main Run Method
	 */
	virtual void operator()() = 0;


	/**
	 * GETTER - SETTER
	 * mSymbexContexts
	 */
	/**
	 * GETTER - SETTER
	 * mSymbexContexts
	 */
	inline virtual void appendSymbexContext(ExecutionContext * anEC)
	{
		mSymbexContexts.append(anEC);
	}


	inline ListOfExecutionContext & getSymbexContexts()
	{
		return( mSymbexContexts );
	}

	inline bool hasSymbexContext() const
	{

		return( mSymbexContexts.nonempty() );
	}


	inline ExecutionContext * popFirstSymbexContext()
	{
		return( mSymbexContexts.pop_first() );
	}

	inline void removeSymbexContext(ExecutionContext * anEC)
	{
		mSymbexContexts.remove( anEC );
	}


	/**
	 * Handle Request
	 * Release
	 * Stop
	 */
	inline void handleRequestGoalAchieved()
	{
		RunnableElement::setLifecycleIdle();
	}

	inline void handleRequestNoWork()
	{
//		RunnableElement::setLifecycleIdle();
		RunnableElement::setLifecycleSuspended();

//		AVM_OS_FATAL_ERROR_EXIT
//				<< "[BUG] Unexpected <NoWork> request !!!"
//				<< SEND_EXIT;
	}

	inline void handleRequestRelease()
	{
		RunnableElement::setLifecycleReleased();
	}

	inline void handleRequestReset()
	{
		// TODO handleRequestReset
//		mSymbexContexts.clear();
		RunnableElement::setLifecycleIdle();
	}

	inline void handleRequestStop()
	{
		RunnableElement::setLifecycleStopped();
	}

	inline void handleRequestWaiting()
	{
		RunnableElement::setLifecycleWaiting();
	}


	/**
	 * GETTER - SETTER
	 * mSymbexDispatcher
	 */
	inline SymbexDispatcher & getSymbexDispatcher() const
	{
		return( mSymbexDispatcher );
	}

};

}

#endif /*SEW_SYMBEXJOB_H_*/
