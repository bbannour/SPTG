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
#ifndef EXECUTIONCONFIGURATION_H_
#define EXECUTIONCONFIGURATION_H_

#include <common/AvmPointer.h>
#include <common/Element.h>
#include <common/BF.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


class ExecutionConfiguration : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ExecutionConfiguration )
{

	AVM_DECLARE_CLONABLE_CLASS( ExecutionConfiguration )


protected:
	/**
	 * ATTRIBUTES
	 */
	RuntimeID mRuntimeID;

	Message mIOMessage;

	BF mCode;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionConfiguration(const RuntimeID & aRID, const BF & aCode)
	: Element( CLASS_KIND_T( ExecutionConfiguration ) ),
	mRuntimeID( aRID ),
	mIOMessage( ),
	mCode( aCode )
	{
		//!! NOTHING
	}

	ExecutionConfiguration(const RuntimeID & aRID,
			const BF & aCode, const Message & ioMessage)
	: Element( CLASS_KIND_T( ExecutionConfiguration ) ),
	mRuntimeID( aRID ),
	mIOMessage( ioMessage ),
	mCode( aCode )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ExecutionConfiguration(const ExecutionConfiguration & anExecConf)
	: Element( anExecConf ),
	mRuntimeID( anExecConf.mRuntimeID ),
	mIOMessage( anExecConf.mIOMessage ),
	mCode( anExecConf.mCode )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutionConfiguration()
	{
		//!! NOTHING
	}


	/**
	 * Serialization
	 */
	virtual std::string str() const;

	virtual void toStream(OutStream & os) const;



	/**
	 * GETTER - SETTER
	 * mRuntimeID
	 */
	inline const RuntimeID & getRuntimeID() const
	{
		return( mRuntimeID );
	}

	inline bool hasRuntimeID() const
	{
		return( mRuntimeID.valid() );
	}

	inline void setRuntimeID(const RuntimeID & aRID)
	{
		mRuntimeID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * mMessage
	 */
	inline const Message & getIOMessage()
	{
		if( mIOMessage.invalid()
			&& mCode.is< AvmCode >() && mCode.to_ptr< AvmCode >()->nonempty()
			&& mCode.to_ptr< AvmCode >()->first().is< Message >() )
		{
			mIOMessage = mCode.to_ptr< AvmCode >()->first();
		}

		return( mIOMessage );
	}

	inline bool hasIOMessage() const
	{
		return( mIOMessage.valid()
			|| (mCode.is< AvmCode >()
				&& mCode.to_ptr< AvmCode >()->nonempty()
				&& mCode.to_ptr< AvmCode >()->first().is< Message >()) );
	}


	/**
	 * GETTER - SETTER
	 * mCode
	 */
	inline const BF & getCode() const
	{
		return( mCode );
	}

	inline bool hasCode() const
	{
		return( mCode.valid() );
	}

	inline void setCode(const BF & aCode)
	{
		mCode = aCode;
	}

	/**
	 * GETTER - SETTER
	 * Parameter iterator
	 */

	// Operator
	inline bool isOperator() const
	{
		return( mCode.is< Operator >() );
	}

	inline Operator * getOperator() const
	{
		return( isOperator() ? getCode().to_ptr< Operator >() : NULL );
	}


	// AvmCode
	inline bool isAvmCode() const
	{
		return( mCode.is< AvmCode >() );
	}

	inline const BFCode & getAvmCode() const
	{
		return( isAvmCode() ? getCode().bfCode() : BFCode::REF_NULL );
	}

	inline const BFCode & toAvmCode() const
	{
		return( getCode().bfCode() );
	}

	inline AVM_OPCODE getAvmOpCode() const
	{
		return( isAvmCode() ? mCode.to_ptr< AvmCode >()->getAvmOpCode()
				: AVM_OPCODE_NULL );
	}

	inline AVM_OPCODE getOptimizedOpCode() const
	{
		return( isAvmCode() ? mCode.to_ptr< AvmCode >()->getOptimizedOpCode()
				: AVM_OPCODE_NULL );
	}


	// AvmProgram - AvmTransition - AvmRoutine
	inline bool isTransition() const
	{
		return( mCode.is< AvmTransition >() );
	}

	inline AvmTransition * getTransition() const
	{
		return( isTransition() ? getCode().to_ptr< AvmTransition >() : NULL );
	}

	inline AvmTransition * toTransition() const
	{
		return( getCode().to_ptr< AvmTransition >() );
	}

	inline bool isRoutine() const
	{
		return( mCode.is_exactly< AvmProgram >() &&
				getCode().to_ptr< AvmProgram >()->isScopeRoutine() );
	}

	inline bool isRunnable() const
	{
		return( mCode.is_exactly< AvmProgram >() &&
				getCode().to_ptr< AvmProgram >()->isScopeRoutine() );
	}


	inline bool isProgram() const
	{
		return( mCode.is_exactly< AvmProgram >() );
	}

	inline bool isWeakProgram() const
	{
		return( mCode.is< AvmProgram >() );
	}

	inline AvmProgram * getProgram() const
	{
		return( isWeakProgram() ? getCode().to_ptr< AvmProgram >() : NULL );
	}

	inline AvmProgram * toProgram() const
	{
		return( getCode().to_ptr< AvmProgram >() );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline int compare(const ExecutionConfiguration & other) const
	{
		int cmpResult = mRuntimeID.compare( other.mRuntimeID );

		return( (cmpResult == 0) ? mCode.compare( other.mCode ) : cmpResult );
	}


};



}

#endif /*EXECUTIONCONFIGURATION_H_*/
