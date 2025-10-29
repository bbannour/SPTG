/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACESEQUENCE_H_
#define TRACESEQUENCE_H_

#include <common/Element.h>

#include <collection/BFContainer.h>
#include <collection/Vector.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>
#include <collection/List.h>


namespace sep
{

class Bitset;

class ExecutionContext;

class ObjectElement;

class RuntimeID;

class TraceFormatter;
class TracePoint;


class TraceSequence : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TraceSequence )
{

	AVM_DECLARE_CLONABLE_CLASS( TraceSequence )


public:
	/**
	 * ATTRIBUTES
	 */
	const Operator * combinator;

	BFList points;

	const ExecutionContext * mEC;

	std::size_t tid;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceSequence(const ExecutionContext * anEC = nullptr, std::size_t aTID = 0)
	: Element( CLASS_KIND_T( TraceSequence ) ),
	combinator( OperatorManager::OPERATOR_SEQUENCE ),
	points( ),
	mEC( anEC ),
	tid( aTID )
	{
		//!! NOTHING
	}


	TraceSequence(TraceSequence * aContainer, const Operator * aCombinator)
	: Element( CLASS_KIND_T( TraceSequence ) ),
	combinator( aCombinator ),
	points( ),
	mEC( /*aContainer->mEC*/nullptr ),
	tid( aContainer->tid )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	TraceSequence(class_kind_t aClassKind)
	: Element( aClassKind ),
	combinator( OperatorManager::OPERATOR_SEQUENCE ),
	points( ),
	mEC( nullptr ),
	tid( 0 )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TraceSequence(const TraceSequence & aTrace)
	: Element( aTrace ),
	combinator( aTrace.combinator ),
	points( aTrace.points ),
	mEC( aTrace.mEC ),
	tid( aTrace.tid )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceSequence()
	{
		//!! NOTHING
	}


	/**
	 * copy an existing trace
	 */
	inline void copyTrace(TraceSequence & aTraceElement)
	{
		combinator = aTraceElement.combinator;

		points.append( aTraceElement.points );

		mEC = aTraceElement.mEC;

		tid = aTraceElement.tid;
	}


	/**
	 * GETTER - SETTER
	 * APPEND -- SAVE
	 * POP_FRONT
	 * SIZE
	 * points
	 */
	inline void append( const BF & bfTP )
	{
		points.append( bfTP );
	}

	inline void save( Element * aTP )
	{
		points.append( BF( aTP) );
	}


	inline void clear()
	{
		points.clear();
	}


	inline virtual std::size_t size() const override
	{
		return( points.size() );
	}


	/**
	 * [RE]SET TracePoint ID
	 */
	void resetTracePointID();

	void setTracePointID(std::size_t intialTPID = 0);


	/**
	 * Contains an Object
	 * points
	 */
	bool containsObject(const ObjectElement  * anObject) const;

	bool containsPoint(const TracePoint * aPoint, BF & foundPoint) const;

	bool containsPoint(const TracePoint * aPoint, bool withValue = true) const;


	/**
	 * Comparison
	 */
	AVM_OPCODE compare(const TraceSequence * otherTraceElt) const;

	inline bool operator==(const TraceSequence & otherTraceElt) const
	{
		return( compare(& otherTraceElt) == AVM_OPCODE_EQ );
	}


	////////////////////////////////////////////////////////////////////////////
	// LIFELINE API
	////////////////////////////////////////////////////////////////////////////

	std::size_t toLifeline(TraceSequence & lifelineTrace,
			const RuntimeID & lifelineRID) const;

	bool lifelineContains(const RuntimeID & lifelineRID,
			const TracePoint & aTracePoint) const;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual std::string str() const override
	{
		return( OSS() << "trace#" << tid );
	}

	inline virtual void toStream(OutStream & out) const override
	{
		toStream(out, AVM_NUMERIC_MAX_SIZE_T);
	}

	void toStream(OutStream & out, std::size_t printCount) const;

	void toStream(OutStream & out,
			const Bitset & coverageBitSet, std::size_t printCount) const;

};


/**
 * operator<<
 */
AVM_OS_STREAM( TraceSequence )


} /* namespace sep */

#endif /* TRACESEQUENCE_H_ */
