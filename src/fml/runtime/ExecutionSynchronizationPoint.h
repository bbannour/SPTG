/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXECUTIONSYNCHRONIZATIONPOINT_H_
#define EXECUTIONSYNCHRONIZATIONPOINT_H_


#include <common/AvmObject.h>

#include <fml/executable/RoutingData.h>
#include <fml/runtime/Message.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


class RuntimeID;


/**
 * TYPE DECLARATIONS
 */

enum AWAITING_POINT_NATURE
{
	AWAITING_POINT_INPUT_NATURE,

	AWAITING_POINT_OUTPUT_NATURE,


	AWAITING_POINT_JOIN_NATURE,

	AWAITING_POINT_UNDEFINED_NATURE
};



class ExecutionSynchronizationPoint final : public AvmObject ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionSynchronizationPoint )
{

//	AVM_DECLARE_CLONABLE_CLASS(ExecutionSynchronizationPoint)

public:
	/**
	 * ATTRIBUTES
	 */
	AWAITING_POINT_NATURE mAwaitingPointNature;

	RuntimeID mRID;

	RoutingData mRoutingData;

	Message mMessage;

	ExecutionSynchronizationPoint * next;

private:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionSynchronizationPoint()
	: mAwaitingPointNature( AWAITING_POINT_UNDEFINED_NATURE ),
	mRID( ),
	mRoutingData( ),
	mMessage( ),
	next( nullptr )
	{
		//!! NOTHING
	}

public:
	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionSynchronizationPoint(const ExecutionSynchronizationPoint & anESP)
	: mAwaitingPointNature( anESP.mAwaitingPointNature ),
	mRID( anESP.mRID ),
	mRoutingData( anESP.mRoutingData ),
	mMessage( anESP.mMessage ),
	next( (anESP.next != nullptr) ?
			new ExecutionSynchronizationPoint(*(anESP.next)) : nullptr )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	ExecutionSynchronizationPoint(AWAITING_POINT_NATURE aWaitingPointNature,
			const RuntimeID & aRoutingRID, const RoutingData & aRoutingData,
			const Message & aMessage,
			ExecutionSynchronizationPoint * nxt = nullptr)
	: mAwaitingPointNature( aWaitingPointNature ),
	mRID( aRoutingRID ),
	mRoutingData( aRoutingData ),
	mMessage( aMessage ),
	next( nxt )
	{
		//!! NOTHING
	}

	ExecutionSynchronizationPoint(AWAITING_POINT_NATURE aWaitingPointNature,
			const RuntimeID & joinRID,
			ExecutionSynchronizationPoint * nxt = nullptr)
	: mAwaitingPointNature( aWaitingPointNature ),
	mRID( joinRID ),
	mRoutingData( ),
	mMessage( ),
	next( nxt )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionSynchronizationPoint()
	{
		sep::destroy( next );
	}


	inline bool isInput() const
	{
		return( mAwaitingPointNature == AWAITING_POINT_INPUT_NATURE );
	}

	inline bool isOutput() const
	{
		return( mAwaitingPointNature == AWAITING_POINT_OUTPUT_NATURE );
	}

	inline bool isJoin() const
	{
		return( mAwaitingPointNature == AWAITING_POINT_JOIN_NATURE );
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & out) const override;

	void printTrace(OutStream & out) const;

};


}

#endif /* EXECUTIONSYNCHRONIZATIONPOINT_H_ */
