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

#include <common/BF.h>


namespace sep
{

class Machine;


class InstanceSpecifierPart final :
		public ObjectClassifier,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceSpecifierPart )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceSpecifierPart )


protected:
	/**
	 * ATTRIBUTES
	 */
	BF mModel;

	std::size_t mInitialInstanceCount;
	std::size_t mMaximalInstanceCount;

	std::size_t mPossibleDynamicInstanciationCount;

	bool mModifierAutoStart;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceSpecifierPart(Machine * aContainer,
			const std::string & aNameID = "instance");

	InstanceSpecifierPart(Machine * aContainer, const BF & aModel,
			std::size_t anInitialInstanceCount = 1,
			std::size_t aMaximalInstanceCount = AVM_NUMERIC_MAX_SIZE_T,
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
				mModel.to< ObjectElement >().getFullyQualifiedNameID() :
				mModel.str() );
	}


	/**
	 * GETTER - SETTER
	 * mInitialInstanceCount
	 */
	inline std::size_t getInitialInstanceCount() const
	{
		return( mInitialInstanceCount );
	}

	bool hasInitialInstance() const
	{
		return( mInitialInstanceCount > 0 );
	}

	inline void setInitialInstanceCount(std::size_t anInitialInstanceCount)
	{
		mInitialInstanceCount = anInitialInstanceCount;
	}


	/**
	 * GETTER - SETTER
	 * mMaximalInstanceCount
	 */
	inline std::size_t getMaximalInstanceCount() const
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

	inline void setMaximalInstanceCount(std::size_t aMaximalInstanceCount)
	{
		mMaximalInstanceCount = aMaximalInstanceCount;
	}


	/**
	 * SETTER
	 * mInitialInstanceCount
	 * mMaximalInstanceCount
	 */
	inline void setInstanceCount(
			std::size_t anInitialInstanceCount,
			std::size_t aMaximalInstanceCount)
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
	static void strMultiplicity(OutStream & out,
			std::size_t anInitialCount, std::size_t aMaximalCount,
			const std::string & leftSeparator = "[ ",
			const std::string & rightSeparator = " ]");

	static void strMultiplicity(OutStream & out, std::size_t anInitialCount,
			std::size_t aPossibleDynamicCount, std::size_t aMaximalCount,
			const std::string & leftSeparator = "[ ",
			const std::string & rightSeparator = " ]");

	void header(OutStream & out, bool & hasChevron) const;

	void toStream(OutStream & out) const override;

};


} /* namespace sep */

#endif /* FML_INFRASTRUCTURE_INSTANCESPECIFIERPART_H_ */
