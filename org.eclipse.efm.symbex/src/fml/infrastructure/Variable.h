/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef VARIABLE_H_
#define VARIABLE_H_

#include <fml/common/PropertyElement.h>

#include <common/BF.h>

#include <collection/BFContainer.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Routine.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{

class BehavioralPart;

class Machine;

class ObjectElement;
class Operator;

class PropertyPart;


class Variable : public PropertyElement ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Variable )
{

	AVM_DECLARE_CLONABLE_CLASS( Variable )


protected:
	/**
	 * ATTRIBUTES
	 */
	BF mType;

	BF mValue;

	BF mBinding;

	Routine * onWriteRoutine;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Variable(ObjectElement * aContainer, const BF & aType,
			const std::string & aQualifiedNameID,
			const std::string & aNameID, const BF & aValue = BF::REF_NULL)
	: PropertyElement( CLASS_KIND_T( Variable ),
			aContainer , aQualifiedNameID , aNameID , aNameID ),
	mType( aType ),
	mValue( ),

	mBinding( ),

	onWriteRoutine( NULL )
	{
		//!! NOTHING
	}

	Variable(ObjectElement * aContainer,
			const Modifier & aModifier, const BF & aType,
			const std::string & aNameID, const BF & aValue = BF::REF_NULL)
	: PropertyElement(CLASS_KIND_T( Variable ), aContainer, aModifier, aNameID),
	mType( aType ),
	mValue( aValue ),

	mBinding( ),

	onWriteRoutine( NULL )
	{
		//!! NOTHING
	}

	Variable(const PropertyPart & aPropertyPart,
			const Modifier & aModifier, const BF & aType,
			const std::string & aNameID, const BF & aValue = BF::REF_NULL);

	Variable(Machine * aContainer, const Modifier & aModifier,
			const Variable * aVariablePattern, const BF & aParam);


	/**
	 * DESTRUCTOR
	 */
	virtual ~Variable()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Qualified Name IDentifier
	 * QualifiedNameID using mFullyQualifiedNameID & mNameID
	 */
	inline virtual std::string getQualifiedNameID() const
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM, DATA )

		return( getFullyQualifiedNameID() );

AVM_ELSE

		return( PropertyElement::getQualifiedNameID() );

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM, DATA )
	}


	/**
	 * UTIL
	 */
	Operator * getAssignOperator() const;


	/**
	 * GETTER - SETTER
	 * the Type Specifier
	 */
	inline const BF & getType() const
	{
		return( mType );
	}

	inline bool hasType() const
	{
		return( mType.valid() );
	}

	std::string strT();


	inline DataType * getDataType() const
	{
		return( getType().as_ptr< DataType >() );
	}

	inline bool hasDataType()
	{
		return( getType().is< DataType >() );
	}


	inline BaseTypeSpecifier * getTypeSpecifier() const
	{
		return( getType().as_ptr< BaseTypeSpecifier >() );
	}

	inline bool hasTypeSpecifier()
	{
		return( getType().is< BaseTypeSpecifier >() );
	}


	inline std::string strTypeSpecifier() const
	{
		return( DataType::strTypeSpecifier( getType() ) );
	}


	/**
	 * GETTER - SETTER
	 * mValue
	 */
	inline BF & getValue()
	{
		return( mValue );
	}

	inline const BF & getValue() const
	{
		return( mValue );
	}

	inline bool hasValue() const
	{
		return( mValue.valid() );
	}

	inline void setValue(const BF & aValue)
	{
		mValue = aValue;
	}

	inline std::string strValue() const
	{
		return( mValue.str() );
	}

	inline std::string prettyPrintableValue() const
	{
		return( mValue.is< ObjectElement >()
				? mValue.to_ptr< ObjectElement >()->getNameID()
				: mValue.str() );
	}


	/**
	 * GETTER - SETTER
	 * mBinding
	 */
	inline BF & getBinding()
	{
		return( mBinding );
	}

	inline const BF & getBinding() const
	{
		return( mBinding );
	}

	inline bool hasBinding() const
	{
		return( mBinding.valid() );
	}

	inline void setBinding(const BF & aBinding)
	{
		mBinding = aBinding;
	}


	/**
	 * GETTER
	 * BehavioralPart Routine Container
	 */
	BehavioralPart * getContainerOfRoutines() const;

	BehavioralPart * getUniqContainerOfRoutines() const;

	/**
	 * GETTER - SETTER
	 * onWrite
	 */
	inline Routine * getOnWriteRoutine() const
	{
		return( onWriteRoutine );
	}

	inline bool hasOnWrite() const
	{
		return( onWriteRoutine != NULL );
	}

	inline void setOnWriteRoutine(Routine * aWriteRoutine)
	{
		onWriteRoutine = aWriteRoutine;
	}


	/**
	 * Serialization
	 */
	void strParameter(OutStream & os) const
	{
		os << getModifier().toString_not(Modifier::NATURE_PARAMETER_KIND) //<< "var "
				<< strTypeSpecifier() << " " << getNameID();

		if( getModifier().hasNatureMacro() && hasBinding() )
		{
			os << " (::= " << getBinding().str() << ")";
		}
		if( hasValue() )
		{
			os << " = " << strValue();
		}
	}

	void strReturn(OutStream & os) const
	{
		os << getModifier().toString_not(Modifier::DIRECTION_RETURN_KIND) //<< "var "
				<< strTypeSpecifier() << " " << getNameID();

		if( getModifier().hasNatureMacro() && hasBinding() )
		{
			os << " (::= " << getBinding().str() << ")";
		}
		if( hasValue() )
		{
			os << " = " << strValue();
		}
	}


	void strHeader(OutStream & os) const
	{
		os << getModifier().toString() << "var "
			<< strTypeSpecifier() << " " << getFullyQualifiedNameID();

		if( hasBinding() )
		{
			os << " $bind " << getBinding().str();
		}

AVM_IF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID , hasValue() )
	os << " = " << strValue();
AVM_ENDIF_DEBUG_FLAG2_AND( COMPILING , QUALIFIED_NAME_ID )
	}

	void toStream(OutStream & os) const;

	void toStreamParameter(OutStream & os) const;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION for SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef TableOfBF_T< Variable >  TableOfVariable;


}

#endif /* VARIABLE_H_ */
