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

#include <common/Element.h>
#include <common/BF.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


class ExecutionConfiguration final : public Element ,
		AVM_INJECT_STATIC_NULL_REFERENCE( ExecutionConfiguration ),
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

	// The timestamp
	BF mTimestamp;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutionConfiguration(const RuntimeID & aRID, const BF & aCode,
			const BF & aTimestamp = BF::REF_NULL)
	: Element( CLASS_KIND_T( ExecutionConfiguration ) ),
	mRuntimeID( aRID ),
	mIOMessage( ),
	mCode( aCode ),
	mTimestamp( aTimestamp )
	{
		if( mCode.is< AvmCode >()
			&& mCode.to< AvmCode >().hasOperand()
			&& mCode.to< AvmCode >().first().is< Message >() )
		{
			mIOMessage = mCode.to< AvmCode >().first();
		}
	}

	ExecutionConfiguration(const RuntimeID & aRID, const BFCode & aCode,
			const Message & ioMessage, const BF & aTimestamp = BF::REF_NULL)
	: Element( CLASS_KIND_T( ExecutionConfiguration ) ),
	mRuntimeID( aRID ),
	mIOMessage( ioMessage ),
	mCode( aCode ),
	mTimestamp( aTimestamp )
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
	mCode( anExecConf.mCode ),
	mTimestamp( anExecConf.mTimestamp )
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
	 * GETTER
	 * Unique Null Reference
	 */
	inline static ExecutionConfiguration & nullref()
	{
		static ExecutionConfiguration _NULL_(
				RuntimeID::nullref(), BF::REF_NULL);

		return( _NULL_ );
	}


	/**
	 * Serialization
	 */
	virtual std::string str() const override;

	virtual void toStream(OutStream & out) const override;



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
	inline const Message & getIOMessage() const
	{
		return( mIOMessage );
	}

	inline bool hasIOMessage() const
	{
		return( mIOMessage.valid() );
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

	inline const Operator & getOperator() const
	{
		return( isOperator() ?
				getCode().to< Operator >() : Operator::nullref() );
	}


	// AvmCode
	inline bool isAvmCode() const
	{
		return( mCode.is< AvmCode >() );
	}

	inline const BFCode & getAvmCode() const
	{
		return( isAvmCode() ? mCode.bfCode() : BFCode::REF_NULL );
	}

	inline const AvmCode & toAvmCode() const
	{
		return( mCode.to< AvmCode >() );
	}

	inline AVM_OPCODE getAvmOpCode() const
	{
		return( isAvmCode() ? mCode.to< AvmCode >().getAvmOpCode()
				: AVM_OPCODE_NULL );
	}

	inline AVM_OPCODE getOptimizedOpCode() const
	{
		return( isAvmCode() ? mCode.to< AvmCode >().getOptimizedOpCode()
				: AVM_OPCODE_NULL );
	}


	// AvmProgram - AvmTransition - AvmRoutine
	inline bool isTransition() const
	{
		return( mCode.is< AvmTransition >() );
	}

	inline AvmTransition * getTransition() const
	{
		return( isTransition() ? getCode().to_ptr< AvmTransition >() : nullptr );
	}

	inline const AvmTransition & toTransition() const
	{
		return( getCode().to< AvmTransition >() );
	}

	inline bool isRoutine() const
	{
		return( mCode.is_exactly< AvmProgram >() &&
				getCode().to< AvmProgram >().isScopeRoutine() );
	}

	inline bool isRunnable() const
	{
		return( mCode.is_exactly< AvmProgram >() &&
				getCode().to< AvmProgram >().isScopeRoutine() );
	}

	inline bool isRunnableState() const
	{
		return( mCode.is_exactly< ExecutableForm >() &&
				getCode().to< ExecutableForm >().getSpecifier().isFamilyComponentState() );
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
		return( isWeakProgram() ? getCode().to_ptr< AvmProgram >() : nullptr );
	}

	inline const AvmProgram & toProgram() const
	{
		return( getCode().to< AvmProgram >() );
	}


	/**
	 * GETTER - SETTER
	 * mTimestamp
	 */
	inline const BF & getTimestamp() const
	{
		return( mTimestamp );
	}

	inline bool hasTimestamp() const
	{
		return( mTimestamp.valid() );
	}

	inline void setTimestamp(const BF & aTimestamp)
	{
		mTimestamp = aTimestamp;
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
