/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ENUMTYPESPECIFIER_H_
#define ENUMTYPESPECIFIER_H_

#include <fml/type/BaseSymbolTypeSpecifier.h>

#include <common/BF.h>


namespace sep
{

class DataType;


class EnumTypeSpecifier final : public BaseSymbolTypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( EnumTypeSpecifier )
{

	AVM_DECLARE_UNCLONABLE_CLASS(EnumTypeSpecifier)


protected:
	/*
	 * ATTRIBUTES
	 */
	bool mIntervalEnumerationFlag;

	BF mInfimum;
	BF mSupremum;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	EnumTypeSpecifier(const DataType & astType)
	: BaseSymbolTypeSpecifier(CLASS_KIND_T( EnumTypeSpecifier ),
			TYPE_ENUM_SPECIFIER, astType, 1, 1, 0),
			mIntervalEnumerationFlag( false ),
	mInfimum( ),
	mSupremum( )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~EnumTypeSpecifier()
	{
		//!!! NOTHING
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
	 * SETTER
	 * mBound
	 */
	void updateBound();

	void updateBound(avm_integer_t min, avm_integer_t max);


	/**
	 * GETTER - SETTER
	 * mSymbolData
	 */
	bool hasSymbolData(const InstanceOfData & aSymbolData) const;

	bool hasSymbolData(const BF & aSymbol) const;


	bool hasSymbolDataWithValue(const BF & aValue) const;

	const Symbol & getSymbolDataByValue(const BF & aValue) const;


	std::size_t getRandomSymbolOffset() const;

	const Symbol & getRandomSymbolData() const;

	const BF & getRandomSymbolValue() const;



	/**
	 * GETTER
	 * newfresh Enum Value
	 */
	BF newfreshSymbolValue() const;


	/**
	 * SETTER
	 * mBitSize
	 */
	inline virtual void updateSize() override
	{
		setBitSize( mSymbolData.size() );
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	BF minConstraint(const BF & aParam) const;
	BF maxConstraint(const BF & aParam) const;

	virtual bool couldGenerateConstraint() const override;

	virtual BF genConstraint(const BF & aParam) const override;


	/**
	 * Format a value w.r.t. its type
	 */
	inline virtual void formatStream(
			OutStream & out, const BF & bfValue) const override
	{
		if( bfValue.is< InstanceOfData >() &&
			(bfValue.to< InstanceOfData >().getTypeSpecifier().isTEQ(this)) )
		{
AVM_IF_DEBUG_FLAG( DATA )

			out << bfValue.to< InstanceOfData >().getFullyQualifiedNameID();

AVM_DEBUG_ELSE

			out << bfValue.to< InstanceOfData >().getNameID();

AVM_ENDIF_DEBUG_FLAG( DATA )
		}
		else
		{
			const Symbol & aSymbol = getSymbolDataByValue(bfValue);

AVM_IF_DEBUG_FLAG( DATA )

			out << ( aSymbol.valid() ?
					aSymbol.getFullyQualifiedNameID() : bfValue.str() );

AVM_DEBUG_ELSE

			out << ( aSymbol.valid() ? aSymbol.getNameID() : bfValue.str() );

AVM_ENDIF_DEBUG_FLAG( DATA )
		}
	}

	// Due to [-Woverloaded-virtual=]
	using BaseSymbolTypeSpecifier::formatStream;


	/**
	 * Serialization
	 */
	void toStream(OutStream & out) const override;

};


}

#endif /* ENUMTYPESPECIFIER_H_ */
