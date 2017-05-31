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
#ifndef BASECOMPILEDFORM_H_
#define BASECOMPILEDFORM_H_

#include <fml/common/ObjectElement.h>

#include <collection/Typedef.h>


namespace sep
{

class BaseAvmProgram;
class BF;
class OutStream;


class BaseCompiledForm :
		public ObjectElement ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseCompiledForm )
{

protected:
	/**
	 * ATTRIBUTES
	 */
	const ObjectElement * mAstElement;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseCompiledForm(class_kind_t aClassKind,
			BaseAvmProgram * aContainer, const ObjectElement * astElement);

	BaseCompiledForm(class_kind_t aClassKind,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	: ObjectElement( aClassKind , NULL , aFullyQualifiedNameID , aNameID),
	mAstElement( NULL )
	{
		//!! NOTHING
	}

	BaseCompiledForm(class_kind_t aClassKind,
			BaseAvmProgram * aContainer, const std::string & aNameID);


	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement * astElement, const Modifier & aModifier);

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement * astElement, const Modifier & aModifier,
			const std::string & aFullyQualifiedNameID);

	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement * astElement, const Modifier & aModifier,
			const std::string & aFullyQualifiedNameID,
			const std::string & aNameID);

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BaseCompiledForm(const BaseCompiledForm & aCompiledForm)
	: ObjectElement( aCompiledForm ),
	mAstElement( aCompiledForm.mAstElement )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseCompiledForm()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mAstElement
	 */
	inline const ObjectElement * getAstElement() const
	{
		return( mAstElement );
	}

	inline bool isAstElement(const ObjectElement * astElement) const
	{
		return( mAstElement == astElement );
	}

	inline bool hasAstElement() const
	{
		return( mAstElement != NULL );
	}

	inline void setAstElement(const ObjectElement * astElement)
	{
		mAstElement = astElement;

		updateFullyQualifiedNameID();
	}

	inline std::string getAstFullyQualifiedNameID() const
	{
		return( (mAstElement != NULL)?
				mAstElement->getFullyQualifiedNameID() : "<fqn-id:null>" );
	}

	inline std::string getAstNameID() const
	{
		return( (mAstElement != NULL)?
				mAstElement->getNameID() : "<name-id:null>" );
	}


	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline virtual const std::string & getFullyQualifiedNameID() const
	{
		return( USE_ONLY_ID ? getNameID() : mFullyQualifiedNameID );
	}

	virtual void updateFullyQualifiedNameID() = 0;


	/**
	 * GETTER - SETTER
	 * mNameID
	 */
	inline virtual const std::string & getNameID() const
	{
		if( mNameID.empty() )
		{
			//? updateNameID();
			return( NamedElement::UNNAMED_ID );
		}
		return( mNameID );
	}

	virtual void updateNameID()
	{
		mNameID = getAstNameID();
		if( mNameID.empty() || NamedElement::isNull(mNameID) )
		{
			mNameID = NamedElement::extractNameID( mFullyQualifiedNameID );
		}
	}


	virtual void updateUfid(avm_size_t instanceId)
	{
		mFullyQualifiedNameID =
				(OSS() << mFullyQualifiedNameID << '#' << instanceId);

		mNameID  = (OSS() << mNameID  << '#' << instanceId);
	}

	virtual void updateUfid(const std::string & dieseExtension)
	{
		mFullyQualifiedNameID =
				(OSS() << mFullyQualifiedNameID << dieseExtension);

		mNameID  = (OSS() << mNameID  << dieseExtension);
	}


	static bool USE_ONLY_ID;


	/**
	 * GETTER
	 * Compiled Element Name
	 */
	inline std::string getUnrestrictedName() const
	{
		return( getAstNameID() );
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const = 0;

	virtual std::string strHeader() const
	{
		StringOutStream oss;

		strHeader( oss );

		return( oss.str() );
	}


	static void toStreamStaticCom(OutStream & out, const BF & comBF);

	static void toStreamStaticCom(OutStream & out,
			const ListOfInstanceOfBuffer & ieBuffers);

	static void toStreamStaticCom(OutStream & out,
			const ListOfInstanceOfPort & iePorts);

};


}

#endif /*BASECOMPILEDFORM_H_*/
