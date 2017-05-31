/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TYPEDEF_H_
#define TYPEDEF_H_

#include <fml/common/ObjectElement.h>

#include <common/BF.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/infrastructure/Routine.h>


namespace sep
{

class BehavioralPart;

class Machine;

class PropertyPart;



class DataType :
		public ObjectElement ,
		public ITypeSpecifier,
		public IIntervalKind,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( DataType )
{

	AVM_DECLARE_CLONABLE_CLASS( DataType )

protected:
	/**
	 * ATTRIBUTES
	 */
	avm_type_specifier_kind_t mSpecifierKind;

	// for Alias, Interval Support, Container Contents
	BF mTypeSpecifier;

	// for general purpose
	Routine * mConstraintRoutine;

	// for Container
	long mMinimumSize;
	long mMaximumSize;

	// for Structure or Union
	PropertyPart   * mPropertyPart;
	BehavioralPart * mBehavioralSpecification;


	// for Interval
	IIntervalKind::KIND mIntervalKind;

	BF mInfimum;
	BF mSupremum;


private:
	/**
	 * CONSTRUCTOR
	 * Interval
	 */
	DataType(Machine * aContainer, const std::string & aNameID,
			const BF & aTypeSpecifier, IIntervalKind::KIND anIntervalKind,
			const BF & anInfimum, const BF & aSupremum);

	/**
	 * CONSTRUCTOR
	 * Container
	 * Alias
	 */
	DataType(ObjectElement * aContainer, const std::string & aNameID,
			avm_type_specifier_kind_t aSpecifierKind,
			const BF & aTypeSpecifier, long aSize);

	/**
	 * CONSTRUCTOR
	 * Enum
	 * Structure
	 * Union
	 */
	DataType(ObjectElement * aContainer, const std::string & aNameID,
			avm_type_specifier_kind_t aSpecifierKind);


public:

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	DataType(const DataType & aDataType);

	/**
	 * DESTRUCTOR
	 */
	virtual ~DataType();


	/**
	 * GETTER
	 * ITypeSpecifier API
	 */

	inline virtual const BaseTypeSpecifier * thisTypeSpecifier() const
	{
		return( NULL );
	}

	inline virtual avm_type_specifier_kind_t getTypeSpecifierKind() const
	{
		return( mSpecifierKind );
	}


	/**
	 * GETTER - SETTER
	 * mTypeSpecifier
	 */
	inline const BF & getTypeSpecifier() const
	{
		return( mTypeSpecifier );
	}

	inline bool hasTypeSpecifier() const
	{
		return( mTypeSpecifier.valid() );
	}

	inline void setTypeSpecifier(const BF & aType)
	{
		mTypeSpecifier = aType;
	}


	/**
	 * GETTER - SETTER
	 * mConstraint
	 */
	inline Routine * getConstraintRoutine() const
	{
		return( mConstraintRoutine );
	}

	inline bool hasConstraintRoutine() const
	{
		return( mConstraintRoutine != NULL );
	}

	inline void setConstraintRoutine(Routine * aConstraintRoutine)
	{
		mConstraintRoutine = aConstraintRoutine;
	}


	////////////////////////////////////////////////////////////////////////////
	// INTERVAL
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Interval
	 */
	static DataType * newInterval(
			Machine * aContainer, const std::string & aNameID,
			const BF & aTypeSpecifier, IIntervalKind::KIND anIntervalKind,
			const BF & anInfimum, const BF & aSupremum);

	/**
	 * GETTER - SETTER
	 * mIntervalKind
	 * IIntervalKind API
	 */
	inline virtual IIntervalKind::KIND getIntervalKind() const
	{
		return( mIntervalKind );
	}


	/**
	 * GETTER
	 * the Interval TypeSpecifier Support
	 */
	inline const BF & getIntervalTypeSpecifier() const
	{
		return( mTypeSpecifier );
	}


	/**
	 * GETTER - SETTER
	 * mInfimum
	 */
	inline const BF & getIntervalInfimum() const
	{
		return( mInfimum );
	}

	inline bool hasIntervalInfimum() const
	{
		return( mInfimum.valid() );
	}

	inline void setIntervalInfimum(const BF & anInfimum)
	{
		mInfimum = anInfimum;
	}


	/**
	 * GETTER - SETTER
	 * mSupremum
	 */
	inline const BF & getIntervalSupremum()const
	{
		return( mSupremum );
	}

	inline bool hasIntervalSupremum() const
	{
		return( mSupremum.valid() );
	}

	inline void setIntervalSupremum(const BF & aSupremum)
	{
		mSupremum = aSupremum;
	}


	/**
	 * GETTER
	 * Interval Length
	 */
	avm_integer_t getIntervalLength();

	/**
	 * Serialization
	 */
	inline std::string strIso_Interval() const
	{
		return( IIntervalKind::to_string(
				mIntervalKind, mInfimum, mSupremum) );
	}

	inline std::string strT_Interval() const
	{
		if( getFullyQualifiedNameID().empty() || getNameID().empty() )
		{
			return( strIso_Interval() );
		}
		else
		{
			return( getNameID() );
		}
	}

	void toStreamInterval(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// CONTAINER
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Container
	 */
	static DataType * newContainer(
			Machine * aContainer, const std::string & aNameID,
			avm_type_specifier_kind_t aSpecifierKind, long aSize);

	static DataType * newContainer(
			Machine * aContainer, const std::string & aNameID,
			avm_type_specifier_kind_t aSpecifierKind,
			const BF & aTypeSpecifier, long aSize);

	/**
	 * GETTER
	 * the Container TypeSpecifier of contents
	 */
	inline const BF & getContentsTypeSpecifier() const
	{
		return( mTypeSpecifier );
	}

	inline avm_type_specifier_kind_t getContainerSpecifierKind() const
	{
		return( mSpecifierKind );
	}


	/**
	 * GETTER - SETTER
	 * mMinimumSize
	 */
	inline long getMinimumSize() const
	{
		return( mMinimumSize );
	}

	inline void setMinimumSize(long minSize)
	{
		mMinimumSize = minSize;
	}

	/**
	 * GETTER - SETTER
	 * mMaximumSize
	 */
	inline long getMaximumSize() const
	{
		return( mMaximumSize );
	}

	inline void setMaximumSize(long maxSize)
	{
		mMaximumSize = maxSize;
	}


	inline long size()
	{
		return( mMaximumSize );
	}

	inline void setSize(long maxSize)
	{
		mMaximumSize = maxSize;
	}

	/**
	 * SETTER
	 * mMinimumSize
	 * mMaximumSize
	 */
	inline void setSize(long minSize, long maxSize)
	{
		mMinimumSize = minSize;
		mMaximumSize = maxSize;
	}


	/**
	 * Serialization
	 */
	inline static std::string strContainerId(std::string aNameID,
		avm_type_specifier_kind_t aSpecifierKind, const BF & baseT, long aSize)
	{
		return( aNameID.empty() ?
				strContainerId(aSpecifierKind, baseT, aSize)  :  aNameID );
	}

	static std::string strContainerId(
			avm_type_specifier_kind_t aSpecifierKind,
			const BF & baseT, long aSize);

	static std::string strContainerId(
			avm_type_specifier_kind_t aSpecifierKind, long aSize);


	std::string strContainerType() const;

	std::string strT_Container() const
	{
		return( isAnonymID() ? strContainerType() : getNameID() );
	}

	void toStreamContainer(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// ENUMERATIOIN
	// STRUCTURE
	// UNION
	////////////////////////////////////////////////////////////////////////////
	/**
	 * GETTER - SETTER
	 * mPropertyPart
	 */
	inline PropertyPart * getPropertyPart() const
	{
		return( mPropertyPart );
	}

	bool hasProperty() const;

	inline void setPropertyPart(PropertyPart * aPropertyPart)
	{
		mPropertyPart = aPropertyPart;
	}

	/**
	 * GETTER - SETTER
	 * BehavioralPart
	 */
	BehavioralPart * getUniqBehaviorPart();

	inline BehavioralPart * getBehaviorPart() const
	{
		return( mBehavioralSpecification );
	}

	bool hasBehavior() const
	{
		return( mBehavioralSpecification != NULL );
	}


	////////////////////////////////////////////////////////////////////////////
	// ENUMERATIOIN
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Enumeration
	 */
	static DataType * newEnum(
			const PropertyPart & aPropertyPart, const std::string & aNameID);

	/**
	 * GETTER
	 * Enumeration Size
	 */
	avm_size_t getEnumSize();

	/**
	 * GETTER - SETTER
	 * mVariables
	 */
	void appendVariable(const BF & aVariable);

	void saveVariable(Variable * aVariable);


	/**
	 * Serialization
	 */
	void toStreamEnum(OutStream & os) const;



	////////////////////////////////////////////////////////////////////////////
	// STRUCTURE
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Structure
	 */
	static DataType * newStructure(
			const PropertyPart & aPropertyPart, const std::string & aNameID);

	/**
	 * Serialization
	 */
	void toStreamStructure(OutStream & os) const;



	////////////////////////////////////////////////////////////////////////////
	// UNION
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Union
	 */
	static DataType * newUnion(
			const PropertyPart & aPropertyPart, const std::string & aNameID);

	/**
	 * Serialization
	 */
	void toStreamUnion(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// CHOICE
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Union
	 */
	static DataType * newChoice(
			const PropertyPart & aPropertyPart, const std::string & aNameID);

	/**
	 * Serialization
	 */
	void toStreamChoice(OutStream & os) const;




	////////////////////////////////////////////////////////////////////////////
	// ALIAS
	////////////////////////////////////////////////////////////////////////////
	/**
	 * CONSTRUCTOR
	 * Alias
	 */
	static DataType * newAlias(const PropertyPart & aPropertyPart,
			const std::string & aNameID, const BF & aTypeSpecifier);

	/**
	 * Serialization
	 */
	void toStreamAlias(OutStream & os) const;





	/**
	 * Serialization
	 */
	static std::string strTypeSpecifier(const BF & aType);

	inline virtual std::string strT() const
	{
		if( hasTypeContainer() )
		{
			return( strT_Container() );
		}
		else if( isTypedInterval() )
		{
			return( strT_Interval() );
		}

		return( getNameID() );
	}


	virtual void strHeader(OutStream & os) const;

	virtual void toStream(OutStream & os) const;


public:

	/**
	 * ATTRIBUTES
	 */
	static std::string ANONYM_ID;

	inline bool isAnonymID() const
	{
		return( getNameID().empty()
				|| (getNameID().find(ANONYM_ID) == 0) );
	}

};


} /* namespace sep */



#endif /* TYPEDEF_H_ */
