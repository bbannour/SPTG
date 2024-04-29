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
	const ObjectElement & mAstElement;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseCompiledForm(class_kind_t aClassKind,
			BaseAvmProgram * aContainer, const ObjectElement & astElement);

	BaseCompiledForm(class_kind_t aClassKind, const ObjectElement & astElement,
		const std::string & aFullyQualifiedNameID, const std::string & aNameID)
	: ObjectElement( aClassKind , nullptr , aFullyQualifiedNameID , aNameID),
	mAstElement( astElement )
	{
		//!! NOTHING
	}

	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement, const std::string & aNameID);


	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement, const Modifier & aModifier);

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement, const Modifier & aModifier,
			const std::string & aFullyQualifiedNameID);

	BaseCompiledForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement, const Modifier & aModifier,
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
	inline const ObjectElement & getAstElement() const
	{
		return( mAstElement );
	}

	inline const ObjectElement & safeAstElement() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mAstElement.isnotNullObjectReference() )
				<< "Unexpected " << mAstElement.getNameID()
				<< " for " << getFullyQualifiedNameID() << "!!!"
				<< SEND_EXIT;

		return( mAstElement );
	}

	inline bool isAstElement(const ObjectElement & astElement) const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( astElement.isnotNullObjectReference() )
				<< "Unexpected " << astElement.getNameID()
				<< " for " << getFullyQualifiedNameID() << "!!!"
				<< SEND_EXIT;

		return( mAstElement.isTEQ( astElement ) );
	}

	inline bool hasAstElement() const
	{
		return( mAstElement.isnotNullObjectReference() );
	}


	inline std::string getAstFullyQualifiedNameID() const
	{
		return( mAstElement.getFullyQualifiedNameID() );
	}

	inline std::string getAstNameID() const
	{
		return( mAstElement.getNameID() );
	}


	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline virtual const std::string & getFullyQualifiedNameID() const override
	{
AVM_IF_DEBUG_FLAG( QUALIFIED_NAME_ID )

		return( mFullyQualifiedNameID );

AVM_ELSE

		return( ObjectElement::USE_ONLY_ID ?
				getNameID() : mFullyQualifiedNameID );

AVM_ENDIF_DEBUG_FLAG( QUALIFIED_NAME_ID )
	}


	inline const std::string & getFQNameID() const
	{
		return( mFullyQualifiedNameID );
	}

	virtual void updateFullyQualifiedNameID() = 0;


	/**
	 * GETTER - SETTER
	 * mNameID
	 */
	inline virtual const std::string & getNameID() const override
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
		if( mFullyQualifiedNameID.empty() )
		{
			mNameID = ( getAstElement().isNullObjectReference()
						?  ""  :  getAstNameID() );

			if( mNameID.empty() || NamedElement::isNullNameID(mNameID) )
			{
				mNameID = NamedElement::extractNameID( mFullyQualifiedNameID );
			}
		}
		else
		{
			mNameID = NamedElement::extractNameID( mFullyQualifiedNameID );
		}
	}


	virtual void updateUfid(std::size_t instanceId)
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
	virtual void strHeader(OutStream & out) const override = 0;

	virtual std::string strHeader() const override
	{
		StringOutStream oss;

		strHeader( oss );

		return( oss.str() );
	}

};


}

#endif /*BASECOMPILEDFORM_H_*/
