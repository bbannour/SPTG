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
#ifndef FML_COMMON_OBJECTELEMENT_H_
#define FML_COMMON_OBJECTELEMENT_H_

#include <common/NamedElement.h>
#include <fml/common/LifecycleElement.h>
#include <fml/common/ModifierElement.h>
#include <fml/common/TraceableElement.h>

#include <base/ClassKindInfo.h>


namespace sep
{

class BF;
class Machine;
class Modifier;
class PropertyElement;
class WObject;


#define  DEBUG_MEMORY_NEW   AVM_OS_DEBUG << "new:> " \
		<< raw_address() << " : " << strHeader() << std::endl;

#define  DEBUG_MEMORY_DEL   AVM_OS_DEBUG << "del:> " \
		<< raw_address() << " : " << strHeader() << std::endl;


class ObjectElement :
		public NamedElement ,
		public LifecycleImpl,
		public ModifierImpl,
		public TraceableElement,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( ObjectElement )
{

public:
	/*
	 * ATTRIBUTES
	 */
	static bool USE_ONLY_ID;


protected:
	/**
	 * ATTRIBUTES
	 */
	ObjectElement * mContainer;

	const WObject * mWObject;

	avm_offset_t mOwnedOffset;

	avm_offset_t mRuntimeOffset;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: NamedElement( aClassKind ),
	LifecycleImpl( ),
	ModifierImpl( aModifier ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}


	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const Modifier & aModifier,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	: NamedElement( aClassKind , aFullyQualifiedNameID, aNameID ),
	LifecycleImpl( ),
	ModifierImpl( aModifier ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID,
			const std::string & anUnrestrictedName)
	: NamedElement( aClassKind ,
			aFullyQualifiedNameID, aNameID , anUnrestrictedName ),
	LifecycleImpl( ),
	ModifierImpl( ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	: NamedElement( aClassKind , aFullyQualifiedNameID, aNameID ),
	LifecycleImpl( ),
	ModifierImpl( ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	ObjectElement(class_kind_t aClassKind,
			ObjectElement * aContainer, const std::string & aNameID)
	: NamedElement( aClassKind ,
			makeFullyQualifiedNameID(aContainer, aNameID) ,
			aNameID , aNameID ),
	LifecycleImpl( ),
	ModifierImpl( ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const Modifier & aModifier, const std::string & aNameID)
	: NamedElement( aClassKind ,
			makeFullyQualifiedNameID(aContainer, aNameID) ,
			aNameID , aNameID ),
	LifecycleImpl( ),
	ModifierImpl( aModifier ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	/**
	 * CONSTRUCTOR
	 * Using pattern
	 */
	ObjectElement(class_kind_t aClassKind,
			ObjectElement * aContainer, const ObjectElement & aPattern)
	: NamedElement( aClassKind ,
			makeFullyQualifiedNameID(aContainer, aPattern.getNameID()) ,
			aPattern.getNameID() , aPattern.getUnrestrictedName() ),
	LifecycleImpl( ),
	ModifierImpl( aPattern.getModifier() ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}

	ObjectElement(class_kind_t aClassKind, ObjectElement * aContainer,
			const Modifier & aModifier, const ObjectElement & aPattern)
	: NamedElement( aClassKind ,
			makeFullyQualifiedNameID(aContainer, aPattern.getNameID()) ,
			aPattern.getNameID() , aPattern.getUnrestrictedName() ),
	LifecycleImpl( ),
	ModifierImpl( aModifier ),
	TraceableElement( ),
	mContainer( aContainer ),
	mWObject( nullptr ),
	mOwnedOffset( 0 ),
	mRuntimeOffset( 0 )
	{
		//!! DEBUG_MEMORY_NEW;
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ObjectElement(const ObjectElement & objElement)
	: NamedElement( objElement ),
	LifecycleImpl( objElement ),
	ModifierImpl( objElement ),
	TraceableElement( objElement ),
	mContainer( objElement.mContainer ),
	mWObject( objElement.mWObject ),
	mOwnedOffset( objElement.mOwnedOffset ),
	mRuntimeOffset( objElement.mRuntimeOffset )
	{
		//!! DEBUG_MEMORY_NEW;
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~ObjectElement()
	{
		//!! DEBUG_MEMORY_DEL;
	}


	/**
	 * VALIDITY TEST
	 * _NULL_
	 */
	inline bool isNullObjectReference() const
	{
		return( getModifier().isNullFlagEnabled() );
	}

	inline bool isnotNullObjectReference() const
	{
		return( getModifier().isNullFlagDisabled() );
	}


	/**
	 * SETTER
	 * Fully Qualified Name IDentifier
	 * mFullyQualifiedNameID
	 * mNameID
	 */
	void updateFullyQualifiedNameID()
	{
		mFullyQualifiedNameID =
				makeFullyQualifiedNameID(getContainer(), getNameID());
	}

	void fullyUpdateAllNameID(const std::string & aNameID)
	{
		mFullyQualifiedNameID =
				makeFullyQualifiedNameID(getContainer(), aNameID);

		mNameID = aNameID;

		if( mUnrestrictedName.empty() )
		{
			mUnrestrictedName = mNameID;
		}
	}


	/**
	 * UTIL
	 * return <container-fully-qulified-name-id>.<name-id>
	 */
	static std::string makeFullyQualifiedNameID(
			const ObjectElement * aContainer, const std::string & aNameID);


	/**
	 * GETTER - SETTER
	 * mContainer
	 */
	inline ObjectElement * getContainer() const
	{
		return( mContainer );
	}

	inline bool hasContainer() const
	{
		return( mContainer != nullptr );
	}

	inline void setContainer(ObjectElement * aContainer)
	{
		mContainer = aContainer;
	}

	inline void updateContainer(ObjectElement * aContainer)
	{
		mContainer = aContainer;

		updateFullyQualifiedNameID();
	}

	/*
	 * UTIL
	 * the first specific type container
	 */
	virtual bool isContainerMachine() const;

	virtual Machine * getContainerMachine() const;

	virtual PropertyElement * getContainerProperty() const;


	/**
	 * GETTER - SETTER
	 * "design" of a USER FORM
	 */
	inline const WObject * getWObject() const
	{
		return( mWObject );
	}

	inline bool hasWObject() const
	{
		return( mWObject != nullptr );
	}

	inline void setWObject(const WObject * wfObject)
	{
		mWObject = wfObject;
	}


	/**
	 * GETTER - SETTER
	 * mOwnedOffset
	 */
	inline avm_offset_t getOwnedOffset() const
	{
		return( mOwnedOffset );
	}

	inline void setOwnedOffset(avm_offset_t anOwnedOffset)
	{
		mOwnedOffset = anOwnedOffset;
	}

	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getRuntimeOffset() const
	{
		return( mRuntimeOffset );
	}

	inline void setRuntimeOffset(avm_offset_t aRuntimeOffset)
	{
		mRuntimeOffset = aRuntimeOffset;
	}


	/**
	 * Serialization
	 */
	inline virtual std::string strHeader() const
	{
		StringOutStream oss;

		strHeader( oss );

		return( oss.str() );
	}

	inline virtual void strHeader(OutStream & out) const
	{
		out << getModifier().toString() << getFullyQualifiedNameID();

		if( hasUnrestrictedName() )
		{
			out << " \"" << getUnrestrictedName() << "\"";
		}
	}


	static void toStreamStaticCom(OutStream & out, const BF & comBF);

};


}

#endif /*FML_COMMON_OBJECTELEMENT_H_*/
