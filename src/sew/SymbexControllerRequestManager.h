/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SEW_SYMBEX_CONTROLLER_REQUEST_MANAGER_H_
#define SEW_SYMBEX_CONTROLLER_REQUEST_MANAGER_H_

#include "SymbexJob.h"
#include "SymbexControllerRequestStatus.h"

#include <util/avm_numeric.h>
#include <collection/List.h>

#include  <famcore/api/AbstractProcessorUnit.h>

#include <sew/SymbexControllerUnitManager.h>


namespace sep
{

class OutStream;


class SymbexControllerRequestManager  :
		public SymbexJob,
		public SymbexControllerRequestStatus
{

	AVM_DECLARE_UNCLONABLE_CLASS(SymbexControllerRequestManager)

public:
	/**
	 * TYPEDEF
	 */
	typedef List< AbstractProcessorUnit * >  ListOfProcessorUnit;


protected:
	/**
	 * ATTRIBUTE
	 */
	ListOfProcessorUnit mRequestStopListener;
	ListOfProcessorUnit mRequestReleaseListener;

	ListOfProcessorUnit mRequestResetListener;

	ListOfProcessorUnit mRequestRestartListener;
	ListOfProcessorUnit mRequestContinueListener;

	ListOfProcessorUnit mRequestRequeueWaitingListener;
	ListOfProcessorUnit mRequestRequeueReserveListener;

	ListOfProcessorUnit mRequestHeuristicListener;

	ListOfProcessorUnit mRequestGoalAchievedListener;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	ListOfProcessorUnit mFireRequestListener;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexControllerRequestManager(SymbexDispatcher & aSymbexDispatcher,
			const WObject * wfParameterObject,
			SymbexControllerUnitManager & aCentralControllerUnit)
	: SymbexJob(aSymbexDispatcher, wfParameterObject, aCentralControllerUnit),
	SymbexControllerRequestStatus( REQUEST_UNDEFINED_STATUS ),

	mRequestStopListener( ),
	mRequestReleaseListener( ),

	mRequestResetListener( ),

	mRequestRestartListener( ),
	mRequestContinueListener( ),

	mRequestRequeueWaitingListener( ),
	mRequestRequeueReserveListener( ),

	mRequestHeuristicListener( ),

	mRequestGoalAchievedListener( ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	mFireRequestListener( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexControllerRequestManager()
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


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////

	void osRequestor(OutStream & os, const std::string & label,
			const ListOfProcessorUnit & listofRequestor);


	/**
	 * REQUEST_STOP_STATUS
	 * mRequestStopListener
	 */
	inline void fireRequestStop()
	{
		fireRequestStopInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestStop();
		}

		mControllerUnitManager.handleRequestStop();
	}

	inline void fireRequestStopInitialize()
	{
		disableRequest( REQUEST_STOP_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestStopListener );
	}


	inline void postRequestStop(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_STOP_STATUS );

		mRequestStopListener.add_unique( aRequestor );
	}


	inline void strStopRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestStopListener);
	}


	/**
	 * REQUEST_RELEASE_STATUS
	 * mRequestReleaseListener
	 */
	inline void fireRequestRelease()
	{
		fireRequestReleaseInitialize();

		AbstractProcessorUnit * aProcessor;
		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first_to( aProcessor );

			mControllerUnitManager.handleRequestRelease(aProcessor);
		}

		mControllerUnitManager.handleRequestRelease();
	}

	inline void fireRequestReleaseInitialize()
	{
		disableRequest( REQUEST_RELEASE_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestReleaseListener );
	}


	inline void postRequestRelease(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_RELEASE_STATUS );

		mRequestReleaseListener.add_unique( aRequestor );
	}


	inline void strReleaseRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestReleaseListener);
	}


	/**
	 * REQUEST_RESET_STATUS
	 * mRequestResetListener
	 */
	inline void fireRequestReset()
	{
		fireRequestResetInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestReset();
		}

		mControllerUnitManager.handleRequestReset();
	}

	inline void fireRequestResetInitialize()
	{
		disableRequest( REQUEST_RESET_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestResetListener );
	}


	inline void postRequestReset(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_RESET_STATUS );

		mRequestResetListener.add_unique( aRequestor );
	}


	inline void strRepostRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestResetListener);
	}


	/**
	 * REQUEST_RESTART_STATUS
	 * mRequestRestartListener
	 */
	inline void fireRequestRestart()
	{
		fireRequestRestartInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestRestart();
		}

		mControllerUnitManager.handleRequestRestart();
	}

	inline void fireRequestRestartInitialize()
	{
		disableRequest( REQUEST_RESTART_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestRestartListener );
	}


	inline void postRequestRestart(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_RESTART_STATUS );

		mRequestRestartListener.add_unique( aRequestor );
	}


	inline void strRestartRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestRestartListener);
	}


	/**
	 * REQUEST_CONTINUE_STATUS
	 * mRequestContinueListener
	 */
	inline void fireRequestContinue()
	{
		fireRequestContinueInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestContinue();
		}

		mControllerUnitManager.handleRequestContinue();
	}

	inline void fireRequestContinueInitialize()
	{
		disableRequest( REQUEST_CONTINUE_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestContinueListener );
	}


	inline void postRequestContinue(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_CONTINUE_STATUS );

		mRequestContinueListener.add_unique( aRequestor );
	}


	inline void strContinueRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestContinueListener);
	}


	/**
	 * REQUEST_REQUEUE_WAITING_STATUS
	 * mRequestRequeueWaitingListener
	 */
	inline void fireRequestRequeueWaiting()
	{
		fireRequestRequeueWaitingInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mControllerUnitManager.handleRequestRequeueWaiting(
					mFireRequestListener.pop_first() );
		}
	}

	inline void fireRequestRequeueWaitingInitialize()
	{
		disableRequest( REQUEST_REQUEUE_WAITING_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestRequeueWaitingListener );
	}


	inline void postRequestRequeueWaiting(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_REQUEUE_WAITING_STATUS );

		mRequestRequeueWaitingListener.add_unique( aRequestor );
	}


	inline void strRequeueWaitingRequestor(
			OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestRequeueWaitingListener);
	}


	/**
	 * REQUEST_REQUEUE_RESERVE_STATUS
	 * mRequestRequeueReserveListener
	 */
	inline void fireRequestRequeueReserve()
	{
		fireRequestRequeueReserveInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mControllerUnitManager.handleRequestRequeueReserve(
					mFireRequestListener.pop_first() );
		}
	}

	inline void fireRequestRequeueReserveInitialize()
	{
		disableRequest( REQUEST_REQUEUE_RESERVE_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestRequeueReserveListener );
	}


	inline void postRequestRequeueReserve(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_REQUEUE_RESERVE_STATUS );

		mRequestRequeueReserveListener.add_unique( aRequestor );
	}


	inline void strRequeueReserveRequestor(
			OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestRequeueReserveListener);
	}


	/**
	 * REQUEST_HEURISTIC_STATUS
	 * mRequestHeuristicListener
	 */
	inline void fireRequestHeuristic()
	{
		fireRequestHeuristicInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestHeuristic();
		}
	}

	inline void fireRequestHeuristicInitialize()
	{
		disableRequest( REQUEST_HEURISTIC_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestHeuristicListener );
	}


	inline void postRequestHeuristic(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_HEURISTIC_STATUS );

		mRequestHeuristicListener.add_unique( aRequestor );
	}


	inline void strHeuristicRequestor(OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestHeuristicListener);
	}


	/**
	 * REQUEST_GOAL_ACHIEVED_STATUS
	 * mRequestGoalAchievedListener
	 */
	inline void fireRequestGoalAchieved()
	{
		SymbexControllerRequestManager::fireRequestGoalAchievedInitialize();

		while( mFireRequestListener.nonempty() )
		{
			mFireRequestListener.pop_first()->handleRequestGoalAchieved();
		}
	}

	inline void fireRequestGoalAchievedInitialize()
	{
		disableRequest( REQUEST_GOAL_ACHIEVED_STATUS );

		mFireRequestListener.clear();
		mFireRequestListener.splice( mRequestGoalAchievedListener );
	}


	inline void postRequestGoalAchieved(AbstractProcessorUnit * aRequestor)
	{
		enableRequest( REQUEST_GOAL_ACHIEVED_STATUS );

		mRequestGoalAchievedListener.add_unique( aRequestor );
	}


	inline void strGoalAchievedRequestor(
			OutStream & os, const std::string & label)
	{
		osRequestor(os, label, mRequestGoalAchievedListener);
	}

};


} /* namespace sep */

#endif /* SEW_SYMBEX_CONTROLLER_REQUEST_MANAGER_H_ */
