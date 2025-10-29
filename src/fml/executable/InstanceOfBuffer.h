/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef INSTANCEOFBUFFER_H_
#define INSTANCEOFBUFFER_H_

#include <fml/executable/BaseInstanceForm.h>

#include <fml/lib/ITypeSpecifier.h>


namespace sep
{

class BaseAvmProgram;
class Buffer;


class InstanceOfBuffer final :
		public BaseInstanceForm,
		AVM_INJECT_STATIC_NULL_REFERENCE( InstanceOfBuffer ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfBuffer )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfBuffer )


protected:
	/*
	 * ATTRIBUTES
	 */
	avm_type_specifier_kind_t mPolicySpecifierKind;

	std::size_t mCapacity;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfBuffer(BaseAvmProgram & aContainer,
			const Buffer & astBuffer, avm_offset_t anOffset);

	InstanceOfBuffer(BaseAvmProgram & aContainer, const Buffer & astBuffer,
			avm_offset_t anOffset, avm_type_specifier_kind_t aSpecifierKind,
			long aCapacity);

	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfBuffer(const InstanceOfBuffer & aBuffer)
	: BaseInstanceForm( aBuffer ),
	mPolicySpecifierKind( aBuffer.mPolicySpecifierKind ),
	mCapacity( aBuffer.mCapacity )
	{
		//!! NOTHING
	}




	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfBuffer(BaseAvmProgram * aContainer,
			const InstanceOfBuffer & aTarget,
			const VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfBuffer ),
			aContainer, aTarget, aRelativeMachinePath),
	mPolicySpecifierKind( aTarget.mPolicySpecifierKind ),
	mCapacity( aTarget.mCapacity )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfBuffer()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static InstanceOfBuffer & nullref();


	/**
	 * GETTER - SETTER
	 * mPolicySpecifierKind
	 */
	inline avm_type_specifier_kind_t getPolicySpecifierKind() const
	{
		return( mPolicySpecifierKind );
	}


	inline bool hasDeterministicPolicy() const
	{
		return( (mPolicySpecifierKind != TYPE_SET_SPECIFIER)
				&& (mPolicySpecifierKind != TYPE_MULTISET_SPECIFIER) );
	}

	inline bool hasNonDeterministicPolicy() const
	{
		return( (mPolicySpecifierKind == TYPE_SET_SPECIFIER)
				|| (mPolicySpecifierKind == TYPE_MULTISET_SPECIFIER) );
	}


	inline void setPolicySpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
	{
		mPolicySpecifierKind = aSpecifierKind;
	}


	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	inline std::size_t getCapacity() const
	{
		return( mCapacity );
	}

	inline long realCapacity() const
	{
		return( (mCapacity == AVM_NUMERIC_MAX_SIZE_T)? -1 : mCapacity );
	}

	inline void setCapacity(long aCapacity)
	{
		mCapacity = (aCapacity < 0) ? AVM_NUMERIC_MAX_SIZE_T : aCapacity;
	}

	inline bool isFinite() const
	{
		return( mCapacity < AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool isInfinite() const
	{
		return( mCapacity == AVM_NUMERIC_MAX_SIZE_T );
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const override;

	virtual void toStream(OutStream & out) const override;

	static void toStream(OutStream & out,
			const ListOfInstanceOfBuffer & ieBuffers);

};


}

#endif /* INSTANCEOFBUFFER_H_ */
