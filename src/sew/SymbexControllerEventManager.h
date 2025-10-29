/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEW_SYMBEX_CONTROLLER_EVENT_MANAGER_H_
#define SEW_SYMBEX_CONTROLLER_EVENT_MANAGER_H_

#include "SymbexJob.h"

#include <collection/List.h>


namespace sep
{

class ExecutionContext;


class IHandlerEventDestroyCtx
{

public:
	/**
	 * DESTRUCTOR
	 */
	virtual ~IHandlerEventDestroyCtx()
	{
		//!! NOTHING
	}

	virtual void handleEventDestroyCtx(ExecutionContext * anEC) = 0;

};



class SymbexControllerEventManager  :  public SymbexJob
{

	AVM_DECLARE_UNCLONABLE_CLASS( SymbexControllerEventManager )

protected:
	/**
	 * TYPEDEFS
	 */
	typedef List< IHandlerEventDestroyCtx * > ListOfHandlerEventDestroyCtx;

protected:
	/**
	 * ATTRIBUTE
	 */
	ListOfHandlerEventDestroyCtx mEventDestroyCtxListener;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	ListOfHandlerEventDestroyCtx::iterator itEventListener;
	ListOfHandlerEventDestroyCtx::iterator endEventListener;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexControllerEventManager(SymbexDispatcher & aSymbexDispatcher,
			const WObject * wfParameterObject,
			SymbexControllerUnitManager & aCentralControllerUnit)
	: SymbexJob(aSymbexDispatcher, wfParameterObject, aCentralControllerUnit),
	mEventDestroyCtxListener( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variable
	itEventListener( ),
	endEventListener( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexControllerEventManager()
	{
		//!! NOTHING
	}

	/**
	 * Thread main Run Method
	 */
	virtual void operator()() override
	{
		//!! NOTHING
	}


	/**
	 * NOTIFICATION
	 * Destroy Execution Context EVENT
	 */
	inline void notifyEventDestroyCtx(ExecutionContext * anEC)
	{
		if( mEventDestroyCtxListener.nonempty() )
		{
			postEventDestroyCtx( anEC );
		}
	}

	void inline postEventDestroyCtx(ExecutionContext * anEC)
	{
		itEventListener  = mEventDestroyCtxListener.begin();
		endEventListener = mEventDestroyCtxListener.end();
		for( ; itEventListener != endEventListener ; ++itEventListener )
		{
			(*itEventListener)->handleEventDestroyCtx( anEC );
		}
	}


	inline void registerHandlerEventDestroyCtx(
			IHandlerEventDestroyCtx * aListener)
	{
		mEventDestroyCtxListener.add_unique( aListener );
	}

	inline void unregisterHandlerEventDestroyCtx(
			IHandlerEventDestroyCtx * aListener)
	{
		mEventDestroyCtxListener.remove( aListener );
	}

};


} /* namespace sep */

#endif /* SEW_SYMBEX_CONTROLLER_EVENT_MANAGER_H_ */
