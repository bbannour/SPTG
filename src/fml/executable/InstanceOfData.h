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

#ifndef INSTANCEOFDATA_H_
#define INSTANCEOFDATA_H_

#include <fml/executable/BaseInstanceForm.h>

#include <collection/BFContainer.h>
#include <collection/TypedefCollection.h>

#include <fml/lib/AvmLang.h>

#include <fml/symbol/TableOfSymbol.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{


class ArrayBF;
class AvmProgram;

class BuiltinArray;
class BaseAvmProgram;

class Element;

class ObjectElement;

class Symbol;


class InstanceOfData final :
		public BaseInstanceForm,
		public IPointerVariableNature,
		AVM_INJECT_STATIC_NULL_REFERENCE( InstanceOfData ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( InstanceOfData )
{

	AVM_DECLARE_CLONABLE_CLASS( InstanceOfData )

	AVM_TYPEDEF_COLLECTION_CLASS( InstanceOfData )

	AVM_TYPEDEF_TABLE_CLASS( InstanceOfData )

protected:
	/*
	 * ATTRIBUTES
	 */
	POINTER_VARIABLE_NATURE mPointerNature;

	// Used to the container of store record/class or array data field instance
	const InstanceOfData * mParent;

	// The Monitor Routine for Assignation
	AvmProgram * mOnWriteRoutine;

	// The initial value
	BF mValue;

	// The initial buffer value
	BF mBufferValue;

	// The variable Field table
	// Used to store record/class or array data field instance
	TableOfSymbol * mAttributeTable;

	// The Relative Data Path for an Instance from this Data Container
	TableOfSymbol * mRelativeDataPath;
	std::size_t * mRelativeOffsetPath;

	// Mark use by some tools like Solver
	avm_offset_t mMark;


public:
	/**
	 * DEFAULT
	 * Empty TableOfSymbol
	 */
	static TableOfSymbol NULL_TABLE_OF_SYMBOL;


public:
	/**
	 * CONSTRUCTOR
	 * copy
	 */
	InstanceOfData(const InstanceOfData & aData)
	: BaseInstanceForm( aData ),
	mPointerNature( aData.mPointerNature ),
	mParent( aData.mParent ),

	mOnWriteRoutine( aData.mOnWriteRoutine ),

	mValue( aData.mValue ),
	mBufferValue( aData.mBufferValue ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( aData.mMark )
	{
		copyAttribute( aData.mAttributeTable );

		copyDataPath( aData.mRelativeDataPath );
	}



	/**
	 * CONSTRUCTOR
	 * Default
	 */
	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier, avm_offset_t anOffset)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer,
			astElement, aTypeSpecifier, anOffset),
	mPointerNature( aPointerNature ),
	mParent( nullptr ),

	mOnWriteRoutine( nullptr ),

	mValue( ),
	mBufferValue( ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aTypeSpecifier.isnotNullref() )
				<< "InstanceOfData:> Unexpected an instance << "
				<< this->getFullyQualifiedNameID()
				<< " >>  without typeSpecifier !!!"
				<< SEND_EXIT;
	}

	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			avm_offset_t anOffset, const Modifier & aModifier)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer,
			astElement, aTypeSpecifier, anOffset, aModifier),
	mPointerNature( aPointerNature ),
	mParent( nullptr ),

	mOnWriteRoutine( nullptr ),

	mValue( ),
	mBufferValue( ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aTypeSpecifier.isnotNullref() )
				<< "InstanceOfData:> Unexpected an instance << "
				<< this->getFullyQualifiedNameID()
				<< " >>  without typeSpecifier !!!"
				<< SEND_EXIT;
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & aFullyQualifiedNameID, avm_offset_t anOffset,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer, astElement,
			aTypeSpecifier, aFullyQualifiedNameID, anOffset, aModifier),
	mPointerNature( aPointerNature ),
	mParent( nullptr ),

	mOnWriteRoutine( nullptr ),

	mValue( ),
	mBufferValue( ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aTypeSpecifier.isnotNullref() )
				<< "InstanceOfData:> Unexpected an instance << "
				<< this->getFullyQualifiedNameID()
				<< " >>  without typeSpecifier !!!"
				<< SEND_EXIT;
	}


	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const ObjectElement & astElement,
			const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & aFullyQualifiedNameID,
			avm_offset_t anOffset, const InstanceOfData & aParent)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer, astElement,
			aTypeSpecifier, aFullyQualifiedNameID, anOffset, aParent),
	mPointerNature( aPointerNature ),
	mParent( & aParent ),

	mOnWriteRoutine( nullptr ),

	mValue( ),
	mBufferValue( ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aTypeSpecifier.isnotNullref() )
				<< "InstanceOfData:> Unexpected an instance << "
				<< this->getFullyQualifiedNameID()
				<< " >>  without typeSpecifier !!!"
				<< SEND_EXIT;
	}


	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			const BaseTypeSpecifier & aTypeSpecifier,
			const std::string & aFullyQualifiedNameID, avm_offset_t anOffset,
			const Modifier & aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), Variable::nullref(),
			aTypeSpecifier, aFullyQualifiedNameID, anOffset, aModifier),
	mPointerNature( aPointerNature ),
	mParent( nullptr ),

	mOnWriteRoutine( nullptr ),

	mValue( ),
	mBufferValue( ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aTypeSpecifier.isnotNullref() )
				<< "InstanceOfData:> Unexpected an instance << "
				<< this->getFullyQualifiedNameID()
				<< " >>  without typeSpecifier !!!"
				<< SEND_EXIT;
	}

	/**
	 * CONSTRUCTOR
	 * for UFI
	 */
	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const InstanceOfData & aParent)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer,
			aParent.getAstElement(), aParent.getTypeSpecifier(), aParent),
	mPointerNature( aPointerNature ),
	mParent( aParent.mParent ),

	mOnWriteRoutine( aParent.mOnWriteRoutine ),

	mValue( aParent.mValue ),
	mBufferValue( aParent.mBufferValue ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		setAliasTarget( aParent );

		copyAttribute( aParent.mAttributeTable );
	}

	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const InstanceOfData & aParent,
			const TableOfSymbol & aRelativeDataPath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer,
			aRelativeDataPath.back().getAstElement(),
			aRelativeDataPath.back().getTypeSpecifier(), aParent),
	mPointerNature( aPointerNature ),
	mParent( aParent.mParent ),

	mOnWriteRoutine( aParent.mOnWriteRoutine ),

	mValue( aParent.mValue ),
	mBufferValue( aParent.mBufferValue ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( new TableOfSymbol(aRelativeDataPath) ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		updateOffsetPath();

		if( aRelativeDataPath.nonempty() )
		{
			setOnWriteRoutine(
					aRelativeDataPath.back().variable().getOnWriteRoutine() );

			setValue( aRelativeDataPath.back().getValue() );

			setBValue( aRelativeDataPath.back().variable().getBValue() );
		}

		setAliasTarget( aParent );
	}

	InstanceOfData(POINTER_VARIABLE_NATURE aPointerNature,
			BaseAvmProgram * aContainer, const InstanceOfData & aParent,
			const TableOfSymbol & aRelativeDataPath, const Symbol & pathLeaf)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer,
			pathLeaf.getAstElement(), pathLeaf.getTypeSpecifier(), aParent),
	mPointerNature( aPointerNature ),
	mParent( aParent.mParent ),

	mOnWriteRoutine( pathLeaf.variable().mOnWriteRoutine ),

	mValue( pathLeaf.variable().mValue ),
	mBufferValue( pathLeaf.variable().mBufferValue ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( new TableOfSymbol(aRelativeDataPath, pathLeaf) ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		updateOffsetPath();

		setAliasTarget( aParent );
	}



	/**
	 * CONSTRUCTOR
	 * for RUNTIME UFI OFFSET
	 */
	InstanceOfData(const InstanceOfData & aModel,
			const InstanceOfData & aRoot, std::size_t * aRelativeOffsetPath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aModel.getContainer(),
			aModel.getAstElement(), aRoot.getTypeSpecifier(), aRoot),
	mPointerNature( POINTER_UFI_RUNTIME_NATURE ),
	mParent( & aModel ),

	mOnWriteRoutine( aModel.mOnWriteRoutine ),

	mValue( aModel.mValue ),
	mBufferValue( aModel.mBufferValue ),

	mAttributeTable( aModel.getAttribute() ),

	mRelativeDataPath( aModel.getDataPath() ),
	mRelativeOffsetPath( aRelativeOffsetPath ),

	mMark( 0 )
	{
		setAllNameID(aModel.getFullyQualifiedNameID(), aModel.getNameID());

		setRuntimeContainerRID( aRoot.getRuntimeContainerRID() );
	}


	/**
	 * CONSTRUCTOR
	 * for Alias
	 */
	InstanceOfData(BaseAvmProgram * aContainer, const InstanceOfData & aTarget,
			const VectorOfInstanceOfMachine & aRelativeMachinePath)
	: BaseInstanceForm(CLASS_KIND_T( InstanceOfData ), aContainer, aTarget,
			aRelativeMachinePath),
	mPointerNature( aTarget.mPointerNature ),
	mParent( aTarget.mParent ),

	mOnWriteRoutine( aTarget.mOnWriteRoutine ),

	mValue( aTarget.mValue ),
	mBufferValue( aTarget.mBufferValue ),

	mAttributeTable( & NULL_TABLE_OF_SYMBOL ),

	mRelativeDataPath( & NULL_TABLE_OF_SYMBOL ),
	mRelativeOffsetPath( nullptr ),

	mMark( 0 )
	{
		copyDataPath( aTarget.mRelativeDataPath );
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~InstanceOfData()
	{
		updateOffsetPath();

		if( (mAttributeTable != (& NULL_TABLE_OF_SYMBOL)) &&
			(mPointerNature != POINTER_UFI_RUNTIME_NATURE) )
		{
			delete( mAttributeTable );
			mAttributeTable = nullptr;
		}

		if( (mRelativeDataPath != (& NULL_TABLE_OF_SYMBOL)) &&
			(mPointerNature != POINTER_UFI_RUNTIME_NATURE) )
		{
			delete( mRelativeDataPath );
			mRelativeDataPath = nullptr;
		}

		delete( mRelativeOffsetPath );
		mRelativeOffsetPath = nullptr;

//		AVM_OS_TRACE << "InstanceOfData::del :> "
////				<< "offset#" << getOffset() << FQN_ID_ROOT_SEPARATOR
//				<< mFullyQualifiedNameID << std::endl;
	}


	/**
	 * GETTER
	 * Unique Null Reference
	 */
	static InstanceOfData & nullref();


	/**
	 * GETTER
	 * Compiled ObjectElement as Compiled Variable
	 */
	inline const Variable & getAstVariable() const
	{
		return( safeAstElement().as< Variable >() );
	}

	inline bool hasAstVariable() const
	{
		return( hasAstElement() && getAstElement().is< Variable >() );
	}


	/**
	 * GETTER
	 * Qualified Name IDentifier
	 * QualifiedNameID using mFullyQualifiedNameID & mNameID
	 */
	inline virtual std::string getQualifiedNameID() const override
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM, DATA )

		return( getFullyQualifiedNameID() );

AVM_ELSE

		return( (isStandardPointer() || isEnumSymbolPointer())
				? makeQualifiedNameID( getFullyQualifiedNameID(), getNameID() )
				: makeQualifiedNameID( getFullyQualifiedNameID() ) );

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM, DATA )
	}

	/**
	 * GETTER
	 * mFullyQualifiedNameID
	 * mNameID
	 */
	virtual std::string getUniqNameID() const override;

	virtual void updateFullyQualifiedNameID() override;

	inline void updateFullyQualifiedNameID(
			const std::string & aFullyQualifiedNameID, const std::string & id)
	{
		setAllNameID( aFullyQualifiedNameID , id );
	}

	/**
	 * GETTER - SETTER
	 * mId
	 */
	void updateNameID() override;



	/**
	 * SETTER
	 * the SharedData
	 */
	inline void setSharedVariable(InstanceOfData * sharedVariable)
	{
		setOffset( sharedVariable->getOffset() );

//		setModifier( sData->getModifier() );

		mOnWriteRoutine = sharedVariable->mOnWriteRoutine;

		mValue = sharedVariable->mValue;

		mBufferValue  = sharedVariable->mBufferValue;
	}

	/**
	 * GETTER - SETTER
	 * mParent
	 */
	inline const InstanceOfData * getParent() const
	{
		return( mParent );
	}

	inline bool hasParent() const
	{
		return( mParent != nullptr );
	}

	inline void setParent(InstanceOfData * aParent)
	{
		mParent = aParent;
	}


	/**
	 * GETTER - SETTER
	 * mAttributeTable
	 */
	inline TableOfSymbol * getAttribute() const
	{
		return( mAttributeTable );
	}

	inline bool hasAttribute() const
	{
		return( (mAttributeTable != (& NULL_TABLE_OF_SYMBOL)) &&
				(mAttributeTable != nullptr) && mAttributeTable->nonempty() );
	}

	inline void setAttribute(TableOfSymbol * anAttributeTable)
	{
		mAttributeTable = ( anAttributeTable != nullptr ) ?
				anAttributeTable : (& NULL_TABLE_OF_SYMBOL);
	}

	inline void copyAttribute(TableOfSymbol * anAttributeTable)
	{
		mAttributeTable = ( anAttributeTable != nullptr ) ?
			new TableOfSymbol(*anAttributeTable) : (& NULL_TABLE_OF_SYMBOL);
	}


	inline void setAttribute(avm_offset_t offset, const Symbol & aWProperty)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasAttribute() )
				<< "setAttribute:> Unexpected a <null> AttributeTable !!!"
				<< SEND_EXIT;

		mAttributeTable->set(offset, aWProperty);
	}

	/**
	 * GETTER - SETTER
	 * mOnWriteRoutine
	 */
	inline AvmProgram * getOnWriteRoutine() const
	{
		return( mOnWriteRoutine );
	}

	const BFCode & getOnWriteCode() const;


	inline bool hasOnWriteRoutine() const
	{
		return( mOnWriteRoutine != nullptr );
	}

	inline void setOnWriteRoutine(AvmProgram * onWriteRoutine)
	{
		mOnWriteRoutine = onWriteRoutine;
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


	// ArrayValue
	ArrayBF * getArrayValue() const;

	bool hasArrayValue() const;

	// BuiltinArrayValue
	BuiltinArray * getBuiltinArrayValue() const;

	bool hasBuiltinArrayValue() const;

	/**
	 * GETTER - SETTER
	 * mBufferValue
	 */

	inline BF & getBValue()
	{
		return( mBufferValue );
	}

	inline const BF & getBValue() const
	{
		return( mBufferValue );
	}

	inline bool hasBValue() const
	{
		return( mBufferValue.valid() );
	}


	inline void setBValue(const BF & aBufferValue)
	{
		mBufferValue = aBufferValue;
	}

	inline void resetBValue(Element * aBufferValue)
	{
		mBufferValue.replacePointer( aBufferValue );
	}


	/**
	 * GETTER - SETTER
	 * mRelativeDataPath
	 */
	inline TableOfSymbol * getDataPath() const
	{
		return( mRelativeDataPath );
	}

	inline bool hasDataPath() const
	{
		return( (mRelativeDataPath != (& NULL_TABLE_OF_SYMBOL))
				&& (mRelativeDataPath != nullptr)
				&& mRelativeDataPath->nonempty() );
	}

	inline void setDataPath(TableOfSymbol * aRelativeDataPath)
	{
		mRelativeDataPath = (aRelativeDataPath != nullptr) ?
				aRelativeDataPath : (& NULL_TABLE_OF_SYMBOL);

		updateOffsetPath();
	}

	inline void copyDataPath(TableOfSymbol * aRelativeDataPath)
	{
		mRelativeDataPath = (aRelativeDataPath != nullptr) ?
			new TableOfSymbol(*aRelativeDataPath) : (& NULL_TABLE_OF_SYMBOL);

		updateOffsetPath();
	}

	inline void setDataPath(const TableOfSymbol & aRelativeDataPath)
	{
		mRelativeDataPath = new TableOfSymbol( aRelativeDataPath );

		updateOffsetPath();
	}


	/**
	 * GETTER - SETTER
	 * mRelativeOffsetPath
	 */
	inline std::size_t * getOffsetPath() const
	{
		return( mRelativeOffsetPath );
	}

	inline std::size_t getOffsetPath(std::size_t idx) const
	{
		return( mRelativeOffsetPath[idx] );
	}

	bool hasOffsetPath() const
	{
		return( mRelativeOffsetPath != nullptr );
	}

	inline void setOffsetPath(std::size_t * anOffsetPath)
	{
		mRelativeOffsetPath = anOffsetPath;
	}

	std::string strOffsetPath(const std::string & tab = "") const;

	void updateOffsetPath();



	/**
	 * GETTER - SETTER
	 * mPointerNature
	 */
	inline virtual POINTER_VARIABLE_NATURE getPointerNature() const override
	{
		return( mPointerNature );
	}

	bool isConcreteArrayIndex() const;

	bool isConcreteStructAttribute() const;


	/**
	 * GETTER - SETTER
	 * mMark
	 */
	inline avm_offset_t getMark() const
	{
		return( mMark );
	}

	inline void eraseMark()
	{
		mMark = 0;
	}

	inline void setMark(avm_offset_t aMark)
	{
		mMark = aMark;
	}



	/**
	 * Format a value w.r.t. its type
	 */
	virtual void formatStream(OutStream & os, const BF & bfValue) const;

	virtual void formatStream(OutStream & os, const ArrayBF & arrayValue) const;


	/**
	 * Serialization
	 */
	void strHeader(OutStream & os) const override;

	std::string strHeaderId() const;

	void toStream(OutStream & os) const override;


	inline void strValue(OutStream & os, const BF & aValue) const
	{
		os << AVM_STR_INDENT; //<< IGNORE_FIRST_TAB;

		if( aValue.valid() )
		{
			formatStream( os << TAB , aValue );
		}
		else
		{
			aValue.toStream( os );
		}

		os << END_INDENT;
	}

	inline void strValue(OutStream & os) const
	{
		strValue( os, mValue );
	}

	inline void strBValue(OutStream & os) const
	{
		strValue( os, mBufferValue );
	}


	inline std::string strValue(const BF & aValue) const
	{
		StringOutStream oss;

		formatStream( oss , aValue );

		return( oss.str() );
	}


	inline std::string strValue() const
	{
		return( mValue.valid() ? strValue(mValue) : mValue.str() );
	}

	inline std::string strBValue() const
	{
		return( mBufferValue.valid() ?
				strValue(mBufferValue) : mBufferValue.str() );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfData
// TYPE DEFINITION for TABLE , SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef  TableOfBF_T< InstanceOfData >  TableOfInstanceOfData;


}

#endif /* INSTANCEOFDATA_H_ */
