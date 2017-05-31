/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 juil. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INTERVALTYPESPECIFIER_H_
#define INTERVALTYPESPECIFIER_H_

#include <fml/type/BaseTypeSpecifier.h>

#include <common/BF.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{

class DataType;


class IntervalTypeSpecifier :
		public BaseTypeSpecifier,
		public IIntervalKind,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( IntervalTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(IntervalTypeSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */

	// the Type Specifier
	TypeSpecifier mSupportTypeSpecifier;

	IIntervalKind::KIND mIntervalKind;

	BF mInfimum;
	BF mSupremum;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IntervalTypeSpecifier(DataType * aCompiledType,
			const TypeSpecifier & aTypeSpecifier,
			IIntervalKind::KIND aNature,
			const BF & anInfimum, const BF & aSupremum)
	: BaseTypeSpecifier(CLASS_KIND_T( IntervalTypeSpecifier ),
			TYPE_INTERVAL_SPECIFIER, aCompiledType, 1,
			aTypeSpecifier.getDataSize(), aTypeSpecifier.getBitSize()),
	mSupportTypeSpecifier( aTypeSpecifier ),
	mIntervalKind( aNature ),
	mInfimum( anInfimum ),
	mSupremum( aSupremum )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~IntervalTypeSpecifier()
	{
		//!!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mSupportTypeSpecifier
	 */
	inline const TypeSpecifier & getSupportTypeSpecifier() const
	{
		return( mSupportTypeSpecifier );
	}

	inline bool hasSupportTypeSpecifier() const
	{
		return( mSupportTypeSpecifier.valid() );
	}

	inline void setSupportTypeSpecifier(const TypeSpecifier & aTypeSpecifier)
	{
		mSupportTypeSpecifier = aTypeSpecifier;
	}


	/**
	 * GETTER - SETTER
	 * mIntervalKind
	 */
	inline virtual IIntervalKind::KIND getIntervalKind() const
	{
		return( mIntervalKind );
	}


	/**
	 * GETTER - SETTER
	 * mInfimum
	 */
	inline const BF & getInfimum() const
	{
		return( mInfimum );
	}

	inline bool hasInfimum() const
	{
		return( mInfimum.valid() );
	}

	inline void setInfimum(const BF & anInfimum)
	{
		mInfimum = anInfimum;
	}


	/**
	 * GETTER - SETTER
	 * mSupremum
	 */
	inline const BF & getSupremum()const
	{
		return( mSupremum );
	}

	inline bool hasSupremum() const
	{
		return( mSupremum.valid() );
	}

	inline void setSupremum(const BF & aSupremum)
	{
		mSupremum = aSupremum;
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	BF minConstraint(const BF & aParam) const;
	BF maxConstraint(const BF & aParam) const;
	BF genConstraint(const BF & aParam) const;


	/**
	 * Serialization
	 */
	inline std::string strIso() const
	{
		return( IIntervalKind::to_string(mIntervalKind, mInfimum, mSupremum) );
	}

	std::string strT() const;

	void toStream(OutStream & os) const;

};


}

#endif /* INTERVALTYPESPECIFIER_H_ */
