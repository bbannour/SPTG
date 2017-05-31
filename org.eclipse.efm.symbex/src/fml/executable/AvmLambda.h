/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 oct. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMLAMBDA_H_
#define AVMLAMBDA_H_



#include <fml/executable/BaseAvmProgram.h>

#include <common/AvmPointer.h>

#include <fml/executable/AvmProgram.h>

#include <fml/expression/AvmCode.h>

#include <collection/Typedef.h>


namespace sep
{


/**
 * TYPE DECLARATIONS
 */

enum AVM_LAMBDA_NATURE
{
	AVM_LAMBDA_APP_NATURE,

	AVM_LAMBDA_FUN_NATURE,

	AVM_LAMBDA_LET_NATURE,

	AVM_LAMBDA_UNDEFINED_NATURE
};



class AvmLambda :
		public BaseAvmProgram ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmLambda )
{

	AVM_DECLARE_CLONABLE_CLASS( AvmLambda )


protected:
	/*
	 * ATTRIBUTES
	 */
	AVM_LAMBDA_NATURE mLambdaNature;

	BF mExpression;

	bool mClosureFlag;


public:
	/**
	 * PREDEFINED UFI
	 */
	static std::string ANONYM_UFI;

	static std::string APP_UFI;

	static std::string FUN_UFI;

	static std::string LET_UFI;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmLambda(BaseAvmProgram * aContainer, avm_size_t aSize,
			AVM_LAMBDA_NATURE aLambdaNature = AVM_LAMBDA_FUN_NATURE)
	: BaseAvmProgram(CLASS_KIND_T( AvmLambda ), aContainer, NULL, aSize),
	mLambdaNature( aLambdaNature ),
	mExpression( ),
	mClosureFlag( false )
	{
		updateFullyQualifiedNameID();

//		AVM_OS_COUT << "new:AvmLambda> " << ((long) this) << " ==> " << std::endl;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmLambda()
	{
//		AVM_OS_COUT << "del:AvmLambda> " << ((long) this) << " ==> " << toString() << std::endl;
	}


	/**
	 * GETTER - SETTER
	 * mLambdaNature
	 */

	inline AVM_LAMBDA_NATURE getNature() const
	{
		return( mLambdaNature );
	}



	inline bool isApp() const
	{
		return( mLambdaNature == AVM_LAMBDA_APP_NATURE );
	}

	inline bool isLambda() const
	{
		return( mLambdaNature == AVM_LAMBDA_FUN_NATURE );
	}

	inline bool isLet() const
	{
		return( mLambdaNature == AVM_LAMBDA_LET_NATURE );
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID();

	inline bool isAnonym() const
	{
		return( fqnEquals( ANONYM_UFI ) );
	}


	/**
	 * GETTER - SETTER
	 * mExpression
	 */
	inline BF & getExpression()
	{
		return( mExpression );
	}

	inline const BF & getExpression() const
	{
		return( mExpression );
	}

	inline bool hasExpression() const
	{
		return( mExpression.valid() );
	}

	inline void setExpression(const BF & aExpression)
	{
		mExpression = aExpression;
	}


	/**
	 * GETTER - SETTER
	 * mClosureFlag
	 */
	inline bool isClosed() const
	{
		return( mClosureFlag );
	}

	inline void setClosed()
	{
		mClosureFlag = true;
	}

	inline void setFree()
	{
		mClosureFlag = false;
	}

	inline void setClosureFlag(bool aClosureFlag)
	{
		mClosureFlag = aClosureFlag;
	}


	inline avm_size_t boundVarCount() const
	{
		return( getData().size() );
	}

//	inline avm_size_t freeVarCount()
//	{
//		return( ( isClosed() )? 0 : '?' );
//	}


	/**
	 * Serialization
	 */
	inline void strHeader(OutStream & os) const
	{
		os << str_indent( this );
	}

	void toStream(OutStream & os) const;

	void toStreamApp(OutStream & os) const;

	void toStreamLambda(OutStream & os) const;

	void toStreamLet(OutStream & os) const;


	/*
	 * Convert to AvmProgram
	 */
	BF convertToProgram(const std::string & id);

};


}

#endif /* AVMLAMBDA_H_ */
