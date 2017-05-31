/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 oct. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXECUTIONLOCATION_H_
#define EXECUTIONLOCATION_H_

#include <common/Element.h>

#include <collection/List.h>

#include <fml/expression/AvmCode.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


class ExecutionLocation :  public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionLocation )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionLocation )

public:
	/**
	 * ATTRIBUTES
	 */
	RuntimeID mRID;

	BFCode mCODE;

	AvmCode::const_iterator itCode;
	AvmCode::const_iterator endCode;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionLocation()
	: Element( CLASS_KIND_T( ExecutionLocation ) ),
	mRID( ),
	mCODE( ),
	itCode( ),
	endCode( )
	{
		//!! NOTHING
	}

public:
	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionLocation(const ExecutionLocation & anExecLocation)
	: Element( CLASS_KIND_T( ExecutionLocation ) ),
	mRID( anExecLocation.mRID ),
	mCODE( anExecLocation.mCODE ),
	itCode( anExecLocation.itCode ),
	endCode( anExecLocation.endCode )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	ExecutionLocation(const RuntimeID & aRID, const BFCode & aCode)
	: Element( CLASS_KIND_T( ExecutionLocation ) ),
	mRID( aRID ),
	mCODE( aCode ),
	itCode( aCode->begin() ),
	endCode( aCode->end() )
	{
		//!! NOTHING
	}

	ExecutionLocation(const RuntimeID & aRID, const BFCode & aCode,
			const AvmCode::const_iterator & it)
	: Element( CLASS_KIND_T( ExecutionLocation ) ),
	mRID( aRID ),
	mCODE( aCode ),
	itCode( it ),
	endCode( aCode->end() )
	{
		//!! NOTHING
	}

	ExecutionLocation(const RuntimeID & aRID, const BFCode & aCode,
			const AvmCode::const_iterator & it,
			const AvmCode::const_iterator & endIt)
	: Element( CLASS_KIND_T( ExecutionLocation ) ),
	mRID( aRID ),
	mCODE( aCode ),
	itCode( it ),
	endCode( endIt )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionLocation()
	{
		//!! NOTHING
	}



	inline void refreshAll()
	{
		itCode = mCODE->begin();
		endCode = mCODE->end();
	}

	inline void refreshBegin()
	{
		itCode = mCODE->begin();
	}

	inline void refreshEnd()
	{
		endCode = mCODE->end();
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	bool isEQ(const ExecutionLocation * el) const
	{
		return( (this == el) ||
				((mRID == el->mRID) && (mCODE == el->mCODE) &&
						(itCode == el->itCode) && (endCode == el->endCode)) );
	}

	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class ExecutionLocationQueue
{

protected:
	/**
	 * ATTRIBUTES
	 */
	List< BF > mQueue;

	List< BF > mCache;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionLocationQueue()
	: mQueue( ),
	mCache( )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionLocationQueue(const ExecutionLocationQueue & anELQ)
	: mQueue( anELQ.mQueue ),
	mCache( anELQ.mCache )
	{
		//!!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionLocationQueue()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mQueue
	 */

	bool empty() const
	{
		return( mQueue.empty() );
	}

	bool nonempty() const
	{
		return( ! mQueue.empty() );
	}


	void popTo(BF & popElem)
	{
		popElem = mQueue.back();

		mQueue.pop_back();
	}


	void push(const RuntimeID & aRID, const BFCode & aCode)
	{
		mCache.push_front(
				BF( new ExecutionLocation(aRID, aCode) ) );
	}

	void push(const RuntimeID & aRID, const BFCode & aCode,
			const AvmCode::const_iterator & it,
			const AvmCode::const_iterator & endIt)
	{
		mCache.push_front(
				BF( new ExecutionLocation(aRID, aCode, it, endIt) ) );
	}


	void pushCache()
	{
		mQueue.splice(mCache);
	}


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION
	////////////////////////////////////////////////////////////////////////////

	void toStream(OutStream & os) const;

};



}

#endif /* EXECUTIONLOCATION_H_ */
