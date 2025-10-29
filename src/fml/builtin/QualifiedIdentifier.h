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
#ifndef FML_EXPRESSION_UFI_H_
#define FML_EXPRESSION_UFI_H_

#include <fml/builtin/BuiltinForm.h>

#include <common/NamedElement.h>


namespace sep
{


class QualifiedIdentifier :
		public BuiltinForm,
		public GenericBuiltinValueString< QualifiedIdentifier >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( QualifiedIdentifier )
{

	AVM_DECLARE_CLONABLE_CLASS( QualifiedIdentifier )

protected:
	/**
	 * ATTRIBUTE
	 */
	bool mPositionalParameterFlag;

	avm_offset_t mPositionOffset;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	QualifiedIdentifier(const std::string & aValue)
	: BuiltinForm( CLASS_KIND_T( QualifiedIdentifier ) ),
	GenericBuiltinValueString( aValue ),
	mPositionalParameterFlag( false ),
	mPositionOffset( 0 )
	{
		//!! NOTHING
	}

	QualifiedIdentifier(const std::string & aValue, avm_offset_t aPositionOffset)
	: BuiltinForm( CLASS_KIND_T( QualifiedIdentifier ) ),
	GenericBuiltinValueString( aValue ),
	mPositionalParameterFlag( true ),
	mPositionOffset( aPositionOffset )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	QualifiedIdentifier(const QualifiedIdentifier & aQID)
	: BuiltinForm( aQID ),
	GenericBuiltinValueString( aQID ),
	mPositionalParameterFlag( aQID.mPositionalParameterFlag ),
	mPositionOffset( aQID.mPositionOffset )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~QualifiedIdentifier()
	{
		//!! NOTHING
	}


	/**
	 * CONVERSION
	 */
	std::string getLocator()
	{
		std::string::size_type sepPos = mValue.find(FQN_ID_ROOT_SEPARATOR);
		if( sepPos != std::string::npos )
		{
			return( mValue.substr(0, sepPos) );
		}
		return( "" );
	}

	bool hasLocator()
	{
		return( mValue.find(FQN_ID_ROOT_SEPARATOR) != std::string::npos );
	}


	inline std::string getContainerQualifiedNameID() const
	{
		return( NamedElement::getContainerQualifiedNameID(mValue) );
	}

	inline std::string getNameID() const
	{
		return( NamedElement::extractNameID(mValue) );
	}


	/**
	 * GETTER - SETTER
	 * mPositionOffset
	 */
	inline bool isPositionalParameter() const
	{
		return( mPositionalParameterFlag );
	}

	inline void sePositionalParameter(bool isPositionalParameter = true)
	{
		mPositionalParameterFlag = isPositionalParameter;
	}


	/**
	 * GETTER - SETTER
	 * mPositionOffset
	 */
	inline avm_offset_t getPositionOffset() const
	{
		return( mPositionOffset );
	}

	inline void sePositiontOffset(avm_offset_t aPositionOffset)
	{
		mPositionOffset = aPositionOffset;
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const override
	{
		os << TAB << mValue;
		if( mPositionalParameterFlag )
		{
			os << ".$" << mPositionOffset;
		}
		AVM_DEBUG_REF_COUNTER(os);
		os << EOL_FLUSH;
	}

	virtual std::string str() const override
	{
		return( mValue );
	}

	inline virtual std::string strNum(
			std::uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( mValue );
	}

};


}

#endif /*FML_EXPRESSION_UFI_H_*/
