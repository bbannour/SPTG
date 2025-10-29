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

#ifndef SEW_SYMBEX_CONTROLLER_REQUEST_STATUS_H_
#define SEW_SYMBEX_CONTROLLER_REQUEST_STATUS_H_

#include <util/avm_numeric.h>
#include <collection/List.h>

#include  <famcore/api/AbstractProcessorUnit.h>


namespace sep
{

class OutStream;


class SymbexControllerRequestStatus
{

public:
	/**
	 * TYPEDEF
	 */
	typedef std::uint16_t  request_status_t;

	enum
	{
		REQUEST_UNDEFINED_STATUS       = 0x0000,


		REQUEST_STOP_STATUS            = 0x0001,

		REQUEST_RELEASE_STATUS         = 0x0002,


		REQUEST_RESET_STATUS           = 0x0010,

		REQUEST_RESTART_STATUS         = 0x0020,

		REQUEST_CONTINUE_STATUS        = 0x0040,


		REQUEST_REQUEUE_WAITING_STATUS = 0x0100,

		REQUEST_REQUEUE_RESERVE_STATUS = 0x0200,

		REQUEST_HEURISTIC_STATUS       = 0x0400,


		REQUEST_GOAL_ACHIEVED_STATUS   = 0x0800,

		// ALIAS
		REQUEST_ALIAS_CONTINUE_STATUS  = REQUEST_CONTINUE_STATUS
		                               | REQUEST_REQUEUE_RESERVE_STATUS
		                               | REQUEST_RESTART_STATUS,
	};

protected:
	/**
	 * ATTRIBUTE
	 */

	/**
	 * Runtime Processor Request
	 * NOTHING | STOP | RESET | RESTART | RELEASE | REQUEUE | HEURISTIC
	 */
	request_status_t mRequestStatus;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexControllerRequestStatus(request_status_t aRequestStatus)
	: mRequestStatus( aRequestStatus )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexControllerRequestStatus()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mRequestStatus
	 */
	inline request_status_t getRequestStatus() const
	{
		return( mRequestStatus );
	}

	inline bool hasRequestStatus() const
	{
		return( mRequestStatus != REQUEST_UNDEFINED_STATUS );
	}

	inline bool noRequestStatus() const
	{
		return( mRequestStatus == REQUEST_UNDEFINED_STATUS );
	}


	inline bool hasRequestStatus(request_status_t aRequestStatus) const
	{
		return( (mRequestStatus & REQUEST_UNDEFINED_STATUS) != 0 );
	}

	inline bool isRequestStatus(request_status_t aRequestStatus) const
	{
		return( mRequestStatus == REQUEST_UNDEFINED_STATUS );
	}

	inline void setRequestStatus(request_status_t aRequest)
	{
		mRequestStatus = aRequest;
	}


	/**
	 * ENABLE - DISABLE
	 * mRequestStatus
	 */
	inline void enableRequest(request_status_t aRequestStatus)
	{
		mRequestStatus = mRequestStatus | aRequestStatus;
	}

	inline void disableRequest(request_status_t aRequestStatus)
	{
		mRequestStatus = mRequestStatus & (~ aRequestStatus);
	}

	inline void disableRequestStatus()
	{
		mRequestStatus = REQUEST_UNDEFINED_STATUS;
	}

	inline bool hasRequestEnabled() const
	{
		return( mRequestStatus != REQUEST_UNDEFINED_STATUS );
	}

	inline bool isRequestDisabled() const
	{
		return( mRequestStatus == REQUEST_UNDEFINED_STATUS );
	}


	/**
	 * TESTER
	 * REQUEST_ALIAS_CONTINUE_STATUS
	 */
	inline bool hasRequestsToContinue() const
	{
		return( (mRequestStatus & REQUEST_ALIAS_CONTINUE_STATUS) != 0 );
	}

	inline bool hasnoRequestsToContinue() const
	{
		return( (mRequestStatus & REQUEST_ALIAS_CONTINUE_STATUS) == 0 );
	}

	/**
	 * REQUEST_STOP_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestStop() const
	{
		return( (mRequestStatus & REQUEST_STOP_STATUS) != 0 );
	}

	inline bool hasnoRequestStop() const
	{
		return( (mRequestStatus & REQUEST_STOP_STATUS) == 0 );
	}

	/**
	 * REQUEST_RELEASE_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestRelease() const
	{
		return( (mRequestStatus & REQUEST_RELEASE_STATUS) != 0 );
	}

	inline bool hasnoRequestRelease() const
	{
		return( (mRequestStatus & REQUEST_RELEASE_STATUS) == 0 );
	}

	/**
	 * REQUEST_RESET_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestReset() const
	{
		return( (mRequestStatus & REQUEST_RESET_STATUS) != 0 );
	}

	inline bool hasnoRequestReset() const
	{
		return( (mRequestStatus & REQUEST_RESET_STATUS) == 0 );
	}

	/**
	 * REQUEST_RESTART_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestRestart() const
	{
		return( (mRequestStatus & REQUEST_RESTART_STATUS) != 0 );
	}

	inline bool hasnoRequestRestart() const
	{
		return( (mRequestStatus & REQUEST_RESTART_STATUS) == 0 );
	}

	/**
	 * REQUEST_CONTINUE_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestContinue() const
	{
		return( (mRequestStatus & REQUEST_CONTINUE_STATUS) != 0 );
	}

	inline bool hasnoRequestContinue() const
	{
		return( (mRequestStatus & REQUEST_CONTINUE_STATUS) == 0 );
	}

	/**
	 * REQUEST_REQUEUE_WAITING_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestRequeueWaiting() const
	{
		return( (mRequestStatus & REQUEST_REQUEUE_WAITING_STATUS) != 0 );
	}

	inline void setRequestRequeueWaiting()
	{
		mRequestStatus = REQUEST_REQUEUE_WAITING_STATUS;
	}

	/**
	 * REQUEST_REQUEUE_RESERVE_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestRequeueReserve() const
	{
		return( (mRequestStatus & REQUEST_REQUEUE_RESERVE_STATUS) != 0 );
	}

	/**
	 * REQUEST_HEURISTIC_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestHeuristic() const
	{
		return( (mRequestStatus & REQUEST_HEURISTIC_STATUS) != 0 );
	}

	inline void setRequestHeuristic()
	{
		mRequestStatus = REQUEST_HEURISTIC_STATUS;
	}

	/**
	 * REQUEST_GOAL_ACHIEVED_STATUS
	 * mRequestStatus
	 */
	inline bool hasRequestGoalAchieved() const
	{
		return( (mRequestStatus & REQUEST_GOAL_ACHIEVED_STATUS) != 0 );
	}

};


} /* namespace sep */

#endif /* SEW_SYMBEX_CONTROLLER_REQUEST_STATUS_H_ */
