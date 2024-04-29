/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASEINSTANCEFORM_H_
#define BASEINSTANCEFORM_H_

#include <base/SmartPointer.h>

#include <fml/executable/BaseCompiledForm.h>

#include <collection/Array.h>

#include <fml/common/ModifierElement.h>
#include <fml/common/ObjectElement.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/type/BaseTypeSpecifier.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 * TYPEDEDEF
 */
typedef Array< InstanceOfMachine * >  ArrayOfInstanceOfMachine;


class BaseAvmProgram;
class InstanceOfMachine;


class BaseInstanceForm :
		public BaseCompiledForm ,
		public ITypeSpecifier ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseInstanceForm )
{

public:
	/**
	* GLOBALS
	* PRETTY PRINTER PROPERTIES
	*/
	static bool EXPRESSION_PRETTY_PRINTER_FQN_BASED;


protected:
	/*
	 * ATTRIBUTES
	 */
	// the Type Specifier
	const BaseTypeSpecifier & mTypeSpecifier;

	avm_offset_t mOffset;


	// The runtime machine container for runtime parameters creation
	RuntimeID mCreatorContainerRID;

	// The runtime machine container for runtime data access optimization
	RuntimeID mRuntimeContainerRID;

	// the Relative Machine Path for an Alias Instance from this Machine Container
	ArrayOfInstanceOfMachine * mRelativeMachinePath;

	const BaseInstanceForm * mAliasTarget;

	std::uint32_t mInstanciationCount;


public:

	/**
	 * CONSTRUCTOR
	 * copy
	 */
	BaseInstanceForm(const BaseInstanceForm & anInstance)
	: BaseCompiledForm( anInstance ),
	mTypeSpecifier( anInstance.mTypeSpecifier ),
	mOffset( anInstance.mOffset ),

	mCreatorContainerRID( anInstance.mCreatorContainerRID ),
	mRuntimeContainerRID( anInstance.mRuntimeContainerRID ),
	mRelativeMachinePath(
			(anInstance.mRelativeMachinePath != nullptr) ?
					new ArrayOfInstanceOfMachine(
							*(anInstance.mRelativeMachinePath)) : nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( anInstance.mInstanciationCount )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseInstanceForm(class_kind_t aClassKind,
			BaseAvmProgram * aContainer, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier, avm_offset_t anOffset)
	: BaseCompiledForm(aClassKind, aContainer, astElement),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( anOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( ),

	mAliasTarget( nullptr ),
	mInstanciationCount( 0 )
	{
		updateFullyQualifiedNameID();
	}

	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			avm_offset_t anOffset, const Modifier & aModifier)
	: BaseCompiledForm(aClassKind, aContainer, astElement, aModifier),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( anOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( ),

	mAliasTarget( nullptr ),
	mInstanciationCount( 0 )
	{
		updateFullyQualifiedNameID();
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & aFullyQualifiedNameID, avm_offset_t anOffset,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: BaseCompiledForm(aClassKind, aContainer,
			astElement, aModifier, aFullyQualifiedNameID),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( anOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( 0 )
	{
		//!! NOTHING
	}


	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & aFullyQualifiedNameID,
			avm_offset_t anOffset, const BaseInstanceForm & aParent)
	: BaseCompiledForm(aClassKind, aContainer, astElement,
			aParent.getModifier(), aFullyQualifiedNameID),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( anOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( 0 )
	{
		//!! NOTHING
	}


	BaseInstanceForm(class_kind_t aClassKind, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			std::string aFullyQualifiedNameID, avm_offset_t anOffset,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: BaseCompiledForm(aClassKind,
			nullptr, astElement, aModifier, aFullyQualifiedNameID),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( anOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( 0 )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * for UFI
	 */
	BaseInstanceForm(class_kind_t aClassKind,
			BaseAvmProgram * aContainer, const BaseInstanceForm & aParent)
	: BaseCompiledForm( aClassKind, aContainer,
			aParent.safeAstElement(), aParent.getModifier(),
			aParent.getFullyQualifiedNameID(), aParent.getNameID() ),
	mTypeSpecifier( aParent.mTypeSpecifier ),
	mOffset( aParent.mOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath(
			( aParent.hasMachinePath() ) ?
					new ArrayOfInstanceOfMachine(
							*(aParent.getMachinePath())) : nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( aParent.mInstanciationCount )
	{
		//!! NOTHING
	}

	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			const BaseInstanceForm & aParent)
	: BaseCompiledForm( aClassKind,
			aContainer, astElement, aParent.getModifier(),
			aParent.getFullyQualifiedNameID(), aParent.getNameID() ),
	mTypeSpecifier( aTypeSpecifier ),
	mOffset( aParent.mOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath(
			( aParent.hasMachinePath() ) ?
					new ArrayOfInstanceOfMachine(
							*(aParent.getMachinePath())) : nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( aParent.mInstanciationCount )
	{
		//!! NOTHING
	}


	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astElement, const BaseInstanceForm & aModel)
	: BaseCompiledForm( aClassKind, aContainer, astElement),
	mTypeSpecifier( aModel.mTypeSpecifier ),
	mOffset( aModel.mOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( ( aModel.hasMachinePath() ) ?
		new ArrayOfInstanceOfMachine( *(aModel.getMachinePath()) ) : nullptr ),

	mAliasTarget( nullptr ),
	mInstanciationCount( aModel.mInstanciationCount )
	{
		updateFullyQualifiedNameID();
	}


	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const BaseInstanceForm & anAliasTarget,
			ArrayOfInstanceOfMachine * aRelativeMachinePath)
	: BaseCompiledForm( aClassKind , aContainer,
			anAliasTarget.safeAstElement(), anAliasTarget.getModifier(),
			anAliasTarget.getFullyQualifiedNameID(),
			anAliasTarget.getNameID() ),
	mTypeSpecifier( anAliasTarget.mTypeSpecifier ),
	mOffset( anAliasTarget.mOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( aRelativeMachinePath ),

	mAliasTarget( & anAliasTarget ),
	mInstanciationCount( anAliasTarget.mInstanciationCount )
	{
		//!! NOTHING
	}


	BaseInstanceForm(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const BaseInstanceForm & anAliasTarget,
			const VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseCompiledForm( aClassKind , aContainer ,
			anAliasTarget.safeAstElement(), anAliasTarget.getModifier(),
			anAliasTarget.getFullyQualifiedNameID(),
			anAliasTarget.getNameID() ),
	mTypeSpecifier( anAliasTarget.mTypeSpecifier ),
	mOffset( anAliasTarget.mOffset ),

	mCreatorContainerRID( ),
	mRuntimeContainerRID( ),
	mRelativeMachinePath( ( aRelativeMachinePath.nonempty() ) ?
			new ArrayOfInstanceOfMachine(aRelativeMachinePath) : nullptr ),

	mAliasTarget( & anAliasTarget ),
	mInstanciationCount( anAliasTarget.mInstanciationCount )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseInstanceForm()
	{
		delete( mRelativeMachinePath );
	}


	/**
	 * GETTER
	 * mContainer
	 */
	BaseAvmProgram * getContainer() const;


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID() override;


	/**
	 * GETTER - SETTER - TESTER
	 * mTypeSpecifier
	 */

	inline const BaseTypeSpecifier & getTypeSpecifier() const
	{
		return( mTypeSpecifier );
	}

	inline const BaseTypeSpecifier * ptrTypeSpecifier() const
	{
		return( & mTypeSpecifier );
	}

	inline const BaseTypeSpecifier & referedTypeSpecifier() const
	{
		return( mTypeSpecifier.isnotNullref() ?
				mTypeSpecifier.referedTypeSpecifier() : mTypeSpecifier );
	}

	inline bool hasTypeSpecifier() const
	{
		return( mTypeSpecifier.isnotNullref() );
	}


	/**
	 * Type Specifier API
	 */
	inline virtual const BaseTypeSpecifier & thisTypeSpecifier() const override
	{
		return( mTypeSpecifier );
	}

	virtual avm_type_specifier_kind_t getTypeSpecifierKind() const override
	{
		return( mTypeSpecifier.getTypeSpecifierKind() );
	}



	/**
	 * GETTER - SETTER
	 * mOffset
	 */
	inline avm_offset_t getOffset() const
	{
		return( mOffset );
	}

	inline void setOffset(avm_offset_t anOffset)
	{
		mOffset = anOffset;
	}


	/**
	 * GETTER - SETTER
	 * mCreatorContainerID
	 */
	inline const RuntimeID & getCreatorContainerRID() const
	{
		return( mCreatorContainerRID );
	}

	inline bool hasCreatorContainerRID() const
	{
		return( mCreatorContainerRID.valid() );
	}

	inline void setCreatorContainerRID(const RuntimeID & aRID)
	{
		mCreatorContainerRID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * mRuntimeContainerID
	 */
	inline const RuntimeID & getRuntimeContainerRID() const
	{
		return( mRuntimeContainerRID );
	}

	inline bool hasRuntimeContainerRID() const
	{
		return( mRuntimeContainerRID.valid() );
	}

	inline void setRuntimeContainerRID(const RuntimeID & aRID)
	{
		mRuntimeContainerRID = aRID;
	}


	/**
	 * GETTER - SETTER
	 * mRelativeMachinePath
	 */
	inline void appendMachinePath(ArrayOfInstanceOfMachine & aliasPath)
	{
		if( mRelativeMachinePath == nullptr )
		{
			mRelativeMachinePath = new ArrayOfInstanceOfMachine(aliasPath);
		}
		else
		{
			mRelativeMachinePath->realloc(aliasPath);
		}
	}

	inline ArrayOfInstanceOfMachine * getMachinePath() const
	{
		return( mRelativeMachinePath );
	}

	inline bool hasMachinePath() const
	{
		return( (mRelativeMachinePath != nullptr) &&
				mRelativeMachinePath->nonempty() );
	}


	inline bool isAlias() const
	{
		return( (mRelativeMachinePath != nullptr) &&
				mRelativeMachinePath->nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mAliasTarget
	 */
	inline const BaseInstanceForm * getAliasTarget() const
	{
		return( mAliasTarget );
	}

	inline bool hasAliasTarget() const
	{
		return( mAliasTarget != nullptr );
	}

	inline void setAliasTarget(const BaseInstanceForm & anAliasTarget)
	{
		mAliasTarget = (& anAliasTarget);
	}

	/**
	 * GETTER - SETTER
	 * mInstanciationCount
	 */
	inline void incrInstanciationCount(std::uint32_t offset = 1)
	{
		mInstanciationCount += offset;
	}

	inline std::uint32_t instanciationCountIncr()
	{
		return( mInstanciationCount++ );
	}

	inline std::uint32_t getInstanciationCount() const
	{
		return( mInstanciationCount );
	}

	inline void setInstanciationCount(std::uint32_t anIndex)
	{
		mInstanciationCount = anIndex;
	}


	/**
	 * is equals
	 */
	inline virtual bool equals(const BaseInstanceForm * anInstance) const
	{
		if( this == anInstance )
		{
			return( true );
		}
		else if( anInstance != nullptr )
		{
			return( (this->getAliasTarget() == anInstance)
					|| (this == anInstance->getAliasTarget())
					|| (this->fqnEquals(
							anInstance->getFullyQualifiedNameID() )) );
		}
		return( false );
	}

	inline virtual bool equals(const BaseInstanceForm & anInstance) const
	{
		if( this == (& anInstance) )
		{
			return( true );
		}
		else
		{
			return( (this->getAliasTarget() == (& anInstance) )
					|| (this == anInstance.getAliasTarget())
					|| (this->fqnEquals(
							anInstance.getFullyQualifiedNameID() )) );
		}
		return( false );
	}


	/**
	 * Serialization
	 */
//	virtual void toStream(OutStream & os) const override;

	inline virtual void toFscn(OutStream & os) const
	{
		os << TAB2 << getFullyQualifiedNameID() << EOL_FLUSH;
	}


	virtual std::string str() const override;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TYPE DEFINITION CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

DEFINE_VECTOR_PTR( BaseInstanceForm )


}

#endif /* BASEINSTANCEFORM_H_ */
