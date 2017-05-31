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

#include <common/AvmPointer.h>
#include <common/Element.h>

#include <collection/BFContainer.h>
#include <collection/Vector.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>
#include <collection/List.h>


namespace sep
{

class ExecutionContext;

class RuntimeID;

class TraceFormatter;
class TracePoint;


class TraceSequence  :
		public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TraceSequence )
{

	AVM_DECLARE_CLONABLE_CLASS( TraceSequence )


public:
	/**
	 * ATTRIBUTES
	 */
	Operator * combinator;

	BFList points;

	const ExecutionContext * mEC;

	avm_size_t tid;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceSequence(const ExecutionContext * anEC = NULL, avm_size_t aTID = 0)
	: Element( CLASS_KIND_T( TraceSequence ) ),
	combinator( OperatorManager::OPERATOR_SEQUENCE ),
	points( ),
	mEC( anEC ),
	tid( aTID )
	{
		//!! NOTHING
	}


	TraceSequence(TraceSequence * aContainer, Operator * aCombinator)
	: Element( CLASS_KIND_T( TraceSequence ) ),
	combinator( aCombinator ),
	points( ),
	mEC( /*aContainer->mEC*/NULL ),
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
	mEC( NULL ),
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


	inline avm_size_t size() const
	{
		return( points.size() );
	}


	/**
	 * Contains an Object
	 * points
	 */
	bool containsObject(BaseCompiledForm  * anObject) const;

	bool containsPoint(TracePoint * aPoint, BF & foundPoint) const;

	bool containsPoint(TracePoint * aPoint, bool withValue = true) const;


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

	avm_size_t toLifeline(TraceSequence & lifelineTrace,
			const RuntimeID & lifelineRID) const;

	bool lifelineContains(const RuntimeID & lifelineRID,
			const TracePoint & aTracePoint) const;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual std::string str() const
	{
		return( OSS() << "trace#" << tid );
	}

	virtual void toStream(OutStream & os) const;

	virtual void traceMinimum(OutStream & os) const;

};


/**
 * operator<<
 */
AVM_OS_STREAM( TraceSequence )


} /* namespace sep */

#endif /* TRACESEQUENCE_H_ */
