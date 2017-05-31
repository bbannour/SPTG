/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 avr. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_INFRASTRUCTURE_INSTANCESPECIFIERPART_H_
#define FML_INFRASTRUCTURE_INSTANCESPECIFIERPART_H_

#include <fml/common/ObjectClassifier.h>
#include <fml/common/ObjectElement.h>

#include <common/AvmPointer.h>
#include <common/BF.h>


namespace sep
{

class Machine;


class InstanceSpecifierPart :
		public ObjectClassifier,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceSpecifierPart )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceSpecifierPart )


protected:
	/**
	 * ATTRIBUTES
	 */
	BF mModel;

	avm_size_t mInitialInstanceCount;
	avm_size_t mMaximalInstanceCount;

	avm_size_t mPossibleDynamicInstanciationCount;

	bool mModifierAutoStart;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceSpecifierPart(Machine * aContainer,
			const std::string & aNameID = "instance");

	InstanceSpecifierPart(Machine * aContainer, const BF & aModel,
			avm_size_t anInitialInstanceCount = 1,
			avm_size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T,
			const std::string & aNameID = "instance");


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceSpecifierPart()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * the Model Specifier
	 */
	inline const BF & getModel() const
	{
		return( mModel );
	}

	inline bool hasModel() const
	{
		return( mModel.valid() );
	}

	inline void setModel(const BF & aModel)
	{
		mModel = aModel;
	}

	inline std::string strModel() const
	{
		return( mModel.is< ObjectElement >() ?
				mModel.to_ptr< ObjectElement >()->getFullyQualifiedNameID() :
				mModel.str() );
	}


	/**
	 * GETTER - SETTER
	 * mInitialInstanceCount
	 */
	inline avm_size_t getInitialInstanceCount() const
	{
		return( mInitialInstanceCount );
	}

	bool hasInitialInstance() const
	{
		return( mInitialInstanceCount > 0 );
	}

	inline void setInitialInstanceCount(avm_size_t anInitialInstanceCount)
	{
		mInitialInstanceCount = anInitialInstanceCount;
	}


	/**
	 * GETTER - SETTER
	 * mMaximalInstanceCount
	 */
	inline avm_size_t getMaximalInstanceCount() const
	{
		return( mMaximalInstanceCount );
	}

	bool hasMaximalInstance() const
	{
		return( mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool hasMaximalNewInstance() const
	{
		return( (mMaximalInstanceCount > 1) &&
				(mMaximalInstanceCount != AVM_NUMERIC_MAX_SIZE_T) );
	}

	inline void setMaximalInstanceCount(avm_size_t aMaximalInstanceCount)
	{
		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	/**
	 * SETTER
	 * mInitialInstanceCount
	 * mMaximalInstanceCount
	 */
	inline void setInstanceCount(
			avm_size_t anInitialInstanceCount,
			avm_size_t aMaximalInstanceCount)
	{
		mInitialInstanceCount = anInitialInstanceCount;

		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	/**
	 * GETTER - SETTER
	 * "autostart" modifier of Instance
	 */
	inline bool isAutoStart() const
	{
		return( mModifierAutoStart );
	}

	inline void setAutoStart(bool bAutoStart = true)
	{
		mModifierAutoStart = bAutoStart;
	}


	/**
	 * Serialization
	 */
	static void strMultiplicity(OutStream & os,
			avm_size_t anInitialCount, avm_size_t aMaximalCount,
			const std::string & leftSeparator = "[ ",
			const std::string & rightSeparator = " ]");

	static void strMultiplicity(OutStream & os, avm_size_t anInitialCount,
			avm_size_t aPossibleDynamicCount, avm_size_t aMaximalCount,
			const std::string & leftSeparator = "[ ",
			const std::string & rightSeparator = " ]");

	void header(OutStream & os, bool & hasChevron) const;

	void toStream(OutStream & os) const;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_INSTANCESPECIFIERPART_H_ */
