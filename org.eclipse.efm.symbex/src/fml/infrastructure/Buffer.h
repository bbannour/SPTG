/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUFFER_H_
#define BUFFER_H_

#include <fml/common/PropertyElement.h>

#include <collection/BFContainer.h>

#include <fml/lib/ITypeSpecifier.h>


namespace sep
{

class BF;
class ObjectElement;
class PropertyPart;


class Buffer : public PropertyElement ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Buffer )
{

	AVM_DECLARE_CLONABLE_CLASS( Buffer )


protected:
	/**
	 * ATTRIBUTES
	 */
	avm_type_specifier_kind_t mPolicySpecifierKind;

	int mSize;

	BFList mMessage;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Buffer(Machine * aContainer, const std::string & id,
			avm_type_specifier_kind_t aSpecifierKind, int aSize);

	Buffer(const PropertyPart & aPropertyPart, const std::string & id,
			avm_type_specifier_kind_t aSpecifierKind, int aSize);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Buffer()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mPolicySpecifierKind
	 */
	inline avm_type_specifier_kind_t getPolicySpecifierKind() const
	{
		return( mPolicySpecifierKind );
	}

	inline void setPolicySpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
	{
		mPolicySpecifierKind = aSpecifierKind;
	}


	/**
	 * GETTER - SETTER
	 * mSize
	 */
	inline avm_size_t getCapacity() const
	{
		return( ( mSize < 0 ) ?  AVM_NUMERIC_MAX_SIZE_T : mSize );
	}

	inline int getSize() const
	{
		return( mSize );
	}

	inline void setSize(int aSize)
	{
		mSize = aSize;
	}


	/**
	 * GETTER - SETTER
	 * mMessage
	 */
	inline BFList & getMessages()
	{
		return( mMessage );
	}

	inline bool hasMessage() const
	{
		return( mMessage.nonempty() );
	}

	inline void appendMessage(const BF & aParameter)
	{
		mMessage.append( aParameter );
	}


	/**
	 * Serialization
	 */
	static std::string str(avm_type_specifier_kind_t aSpecifierKind);
	static std::string str(avm_type_specifier_kind_t aSpecifierKind, long aSize);

	void strMessage(OutStream & os) const;

	void strHeader(OutStream & os) const;

	void toStream(OutStream & os) const;


public:

	/**
	 * ATTRIBUTES
	 */
	static std::string ANONYM_ID;

	inline bool isAnonymID() const
	{
		return( getNameID().empty() || (getNameID().find(ANONYM_ID) == 0) );
	}

};


}

#endif /* BUFFER_H_ */
