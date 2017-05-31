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
#ifndef AVMPROGRAM_H_
#define AVMPROGRAM_H_

#include <fml/executable/BaseAvmProgram.h>

#include <common/AvmPointer.h>

#include <collection/List.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/common/ModifierElement.h>
#include <fml/common/SpecifierElement.h>

#include <fml/type/TableOfTypeSpecifier.h>

#include <fml/infrastructure/Transition.h>


namespace sep
{


class ExecutableForm;

class ObjectElement;

class TableOfAvmProgram;


class AvmProgram :
		public BaseAvmProgram ,
		public IStatementFamily ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( AvmProgram )
{

	AVM_DECLARE_CLONABLE_CLASS( AvmProgram )


protected:
	/*
	 * ATTRIBUTES
	 */
	avm_offset_t mOffset;

	Specifier::SCOPE_KIND mScope;


	avm_offset_t mParamOffset;
	avm_size_t   mParamCount;

	avm_offset_t mReturnOffset;
	avm_size_t   mReturnCount;

	TableOfInstanceOfData mConstData;

	TableOfTypeSpecifier mTableOfTypeSpecifier;

	BFCode mCode;

	// static class of Port/Message/Signal in communicated statement
	BF mCommunicationCode;

	BF mInternalCommunicationCode;

	ListOfInstanceOfPort mInputCom;
	ListOfInstanceOfPort mOutputCom;

	ListOfInstanceOfBuffer mInputEnabledBuffer;
	ListOfInstanceOfPort mInputEnabledCom;
	ListOfInstanceOfPort mInputEnabledSave;

	bool mMutableCommunicationFlag;

	BF mEnvironmentCom;
	BF mEnvironmentInputCom;
	BF mEnvironmentOutputCom;

public:
	/**
	 * STATIC
	 */
	static std::string ANONYM_UFI;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmProgram(Specifier::SCOPE_KIND aScope, AvmProgram * aContainer,
			const ObjectElement * astProgram, avm_size_t aSize)
	: BaseAvmProgram(CLASS_KIND_T( AvmProgram ), aContainer, astProgram, aSize),
	IStatementFamily( AVM_STATEMENT_UNDEFINED_FAMILY ),

	mOffset( 0 ),
	mScope( aScope ),

	mParamOffset( 0 ),
	mParamCount( 0 ),
	mReturnOffset( 0 ),
	mReturnCount( 0 ),

	mConstData( ),
	mTableOfTypeSpecifier( ),

	mCode( ),

	mCommunicationCode( ),
	mInternalCommunicationCode( ),

	mInputCom( ),
	mOutputCom( ),

	mInputEnabledBuffer( ),
	mInputEnabledCom( ),
	mInputEnabledSave( ),

	mMutableCommunicationFlag( false ),

	mEnvironmentCom( ),
	mEnvironmentInputCom( ),
	mEnvironmentOutputCom( )
	{
		updateFullyQualifiedNameID();
	}


	/**
	 * CONSTRUCTOR
	 * Default for Routine
	 */
	AvmProgram(Specifier::SCOPE_KIND aScope, AvmProgram * aContainer,
			const std::string & id, avm_size_t aSize)
	: BaseAvmProgram(CLASS_KIND_T( AvmProgram ), aContainer, id, aSize),
	IStatementFamily( AVM_STATEMENT_UNDEFINED_FAMILY ),

	mOffset( 0 ),
	mScope( aScope ),

	mParamOffset( 0 ),
	mParamCount( 0 ),
	mReturnOffset( 0 ),
	mReturnCount( 0 ),

	mConstData( ),
	mTableOfTypeSpecifier( ),

	mCode( ),

	mCommunicationCode( ),
	mInternalCommunicationCode( ),

	mInputCom( ),
	mOutputCom( ),

	mInputEnabledBuffer( ),
	mInputEnabledCom( ),
	mInputEnabledSave( ),

	mMutableCommunicationFlag( false ),

	mEnvironmentCom( ),
	mEnvironmentInputCom( ),
	mEnvironmentOutputCom( )
	{
		updateFullyQualifiedNameID();
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmProgram(const AvmProgram & aProgram)
	: BaseAvmProgram( aProgram ),
	IStatementFamily( aProgram ),

	mOffset( aProgram.mOffset ),
	mScope( aProgram.mScope ),

	mParamOffset( aProgram.mParamOffset ),
	mParamCount( aProgram.mParamCount ),
	mReturnOffset( aProgram.mReturnOffset ),
	mReturnCount( aProgram.mReturnCount ),

	mConstData( aProgram.mConstData ),
	mTableOfTypeSpecifier( aProgram.mTableOfTypeSpecifier ),

	mCode( aProgram.mCode ),

	mCommunicationCode( aProgram.mCommunicationCode ),
	mInternalCommunicationCode( aProgram.mInternalCommunicationCode ),

	mInputCom( aProgram.mInputCom ),
	mOutputCom( aProgram.mOutputCom ),

	mInputEnabledBuffer( aProgram.mInputEnabledBuffer ),
	mInputEnabledCom( aProgram.mInputEnabledCom ),
	mInputEnabledSave( aProgram.mInputEnabledSave ),

	mMutableCommunicationFlag( aProgram.mMutableCommunicationFlag ),

	mEnvironmentCom( aProgram.mEnvironmentCom ),
	mEnvironmentInputCom( aProgram.mEnvironmentInputCom ),
	mEnvironmentOutputCom( aProgram.mEnvironmentOutputCom )
	{
		// !! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	AvmProgram(class_kind_t aClassKind,
			Specifier::SCOPE_KIND aScope, AvmProgram * aContainer,
			ObjectElement * aCompiled, avm_size_t aSize)
	: BaseAvmProgram(aClassKind, aContainer, aCompiled, aSize),
	IStatementFamily( AVM_STATEMENT_UNDEFINED_FAMILY ),

	mOffset( 0 ),
	mScope( aScope ),

	mParamOffset( 0 ),
	mParamCount( 0 ),
	mReturnOffset( 0 ),
	mReturnCount( 0 ),

	mConstData( ),
	mTableOfTypeSpecifier( ),

	mCode( ),

	mCommunicationCode( ),
	mInternalCommunicationCode( ),

	mInputCom( ),
	mOutputCom( ),

	mInputEnabledBuffer( ),
	mInputEnabledCom( ),
	mInputEnabledSave( ),

	mMutableCommunicationFlag( false ),

	mEnvironmentCom( ),
	mEnvironmentInputCom( ),
	mEnvironmentOutputCom( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmProgram()
	{
		//!! NOTHING
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
	 * mScope
	 */
	inline Specifier::SCOPE_KIND getScope() const
	{
		return( mScope );
	}

	inline bool isScope(Specifier::SCOPE_KIND aScope) const
	{
		return( (mScope == aScope)
				|| ( aScope == Specifier::SCOPE_UNDEFINED_KIND) );
	}

	inline void setScope(Specifier::SCOPE_KIND aScope)
	{
		mScope = aScope;
	}


	inline bool isScopeTransition() const
	{
		return( mScope == Specifier::SCOPE_TRANSITION_KIND );
	}

	inline void setScopeTransition()
	{
		mScope = Specifier::SCOPE_TRANSITION_KIND;
	}

	inline bool isScopeMachine() const
	{
		return( mScope == Specifier::SCOPE_MACHINE_KIND );
	}

	inline void setScopeMachine()
	{
		mScope = Specifier::SCOPE_MACHINE_KIND;
	}


	inline bool isScopeRoutine() const
	{
		return( mScope == Specifier::SCOPE_ROUTINE_KIND );
	}

	inline void setScopeRoutine()
	{
		mScope = Specifier::SCOPE_ROUTINE_KIND;
	}


	inline bool isScopeProgram() const
	{
		return( mScope == Specifier::SCOPE_PROGRAM_KIND );
	}

	inline void setScopeProgram()
	{
		mScope = Specifier::SCOPE_PROGRAM_KIND;
	}


	/**
	 * GETTER - SETTER
	 * mParamOffset
	 * mParamCount
	 */
	inline const BF & getParam(avm_offset_t offset) const
	{
		return( getData().at(offset) );
	}

	inline BaseTypeSpecifier * getParamTypeSpecifier(avm_offset_t offset) const
	{
		return( getData().rawAt(offset)->getTypeSpecifier() );
	}


	inline avm_offset_t getParamOffset() const
	{
		return( mParamOffset );
	}

	inline avm_size_t getParamCount() const
	{
		return( mParamCount );
	}


	inline InstanceOfData * rawParamData(avm_offset_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset , mParamCount )
				<< "Unbound Instance parameter offset !!!"
				<< SEND_EXIT;

		return( mData.rawAt(mParamOffset + offset) );
	}

	inline bool hasParam() const
	{
		return( mParamCount > 0 );
	}

	inline void setParamOffsetCount(avm_offset_t aParamOffset,
			avm_size_t aParamCount)
	{
		mParamOffset = aParamOffset;
		mParamCount  = aParamCount;
	}


	/**
	 * GETTER - SETTER
	 * mReturnOffset
	 * mReturnCount
	 */
	inline const BF & getReturn(avm_offset_t offset) const
	{
		return( getData().at(mReturnOffset + offset) );
	}

	inline BaseTypeSpecifier * getReturnTypeSpecifier(avm_offset_t offset) const
	{
		return( getData().rawAt(mReturnOffset + offset)->getTypeSpecifier() );
	}


	inline avm_offset_t getReturnOffset() const
	{
		return( mReturnOffset );
	}

	inline avm_offset_t returnOffset(avm_offset_t offset) const
	{
		return( mReturnOffset + offset );
	}

	inline avm_size_t getReturnCount() const
	{
		return( mReturnCount );
	}


	inline InstanceOfData * rawReturnData(avm_offset_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset , mReturnCount )
				<< "Unbound Instance parameter offset !!!"
				<< SEND_EXIT;

		return( mData.rawAt(mReturnOffset + offset) );
	}


	inline bool hasReturn() const
	{
		return( mReturnCount > 0 );
	}

	inline void setReturnOffsetCount(avm_offset_t aReturnOffset,
			avm_size_t aReturnCount)
	{
		mReturnOffset = aReturnOffset;
		mReturnCount  = aReturnCount;
	}


	/**
	 * GETTER
	 * mParamCount
	 * mReturnCount
	 */
	inline avm_size_t getParamReturnCount() const
	{
		return( mParamCount + mReturnCount );
	}

	inline bool hasParamReturn() const
	{
		return( (mParamCount + mReturnCount) > 0 );
	}


	/**
	 * SETTER
	 * mFullyQualifiedNameID
	 */
	virtual void updateFullyQualifiedNameID();

	inline bool isAnonym() const
	{
		return( fqnEquals( ANONYM_UFI ) );
	}


	/*
	 * contains DATA
	 */
	inline bool containsData(InstanceOfData * anInstance) const
	{
		return( BaseAvmProgram::containsData(anInstance) ||
				mConstData.contains(anInstance) );
	}


	/**
	 * GETTER - SETTER
	 * mConstData
	 */
	inline void appendConstData(const BF & anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance.to_ptr< InstanceOfData >()->setContainer(this);

		mConstData.append(anInstance);
	}

	inline void saveConstData(InstanceOfData * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		mConstData.save(anInstance);
	}

	inline const TableOfInstanceOfData & getConstData() const
	{
		return( mConstData );
	}


	inline bool hasConstData() const
	{
		return( mConstData.nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mTypeSpecifier
	 */
	inline void appendTypeSpecifier(const TypeSpecifier & aTypeSpecifier)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aTypeSpecifier )
				<< "TypeSpecifier !!!"
				<< SEND_EXIT;

		mTableOfTypeSpecifier.append(aTypeSpecifier);
	}

	inline TableOfTypeSpecifier & getTypeSpecifier()
	{
		return( mTableOfTypeSpecifier );
	}

	inline const TableOfTypeSpecifier & getTypeSpecifier() const
	{
		return( mTableOfTypeSpecifier );
	}


	inline const TypeSpecifier & getTypeSpecifier(avm_offset_t offset) const
	{
		return( mTableOfTypeSpecifier.get(offset) );
	}

	inline const TypeSpecifier & getTypeSpecifier(
			const std::string & aFullyQualifiedNameID) const
	{
		return( mTableOfTypeSpecifier.getByFQNameID(
				aFullyQualifiedNameID ) );
	}


	inline const TypeSpecifier & getTypeSpecifier(
			const ObjectElement * astElement) const
	{
		return( mTableOfTypeSpecifier.getByAstElement(astElement) );
	}


	inline bool hasTypeSpecifier() const
	{
		return( mTableOfTypeSpecifier.nonempty() );
	}



	/**
	 * GETTER
	 * for EnumSymbolData
	 */
	inline const BF & getSymbolData(
			const std::string & aFullyQualifiedNameID) const
	{
		return( mTableOfTypeSpecifier.getSymbolData( aFullyQualifiedNameID ) );
	}

	inline const BF & getSymbolDataByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		return( mTableOfTypeSpecifier.
				getSymbolDataByQualifiedNameID(aQualifiedNameID) );
	}

	inline const BF & getSymbolDataByNameID(const std::string & aNameID) const
	{
		return( mTableOfTypeSpecifier.getSymbolDataByNameID( aNameID ) );
	}

	inline const BF & getSymbolDataByAstElement(
			const ObjectElement * astElement) const
	{
		return( mTableOfTypeSpecifier.getSymbolDataByAstElement(astElement) );
	}


	/**
	 * GETTER - SETTER
	 * mCode
	 */
	inline BFCode & getCode()
	{
		return( mCode );
	}

	inline const BFCode & getCode() const
	{
		return( mCode );
	}

	inline bool hasCode() const
	{
		return( mCode.valid() );
	}

	inline void setCode(const BFCode & aProgram)
	{
		mCode = aProgram;
	}


	/**
	 * GETTER - SETTER
	 * IOpcodeFamily
	 */
	inline virtual void updateOpcodeFamily()
	{
		IStatementFamily::updateStatementFamily( mCode );
	}


	/**
	 * GETTER
	 * any SYMBOL filtering by an optional type specifier family
	 */
	virtual const BF & getSymbol(
			const std::string & aFullyQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const;

	virtual const BF & getSymbolByQualifiedNameID(
			const std::string & aQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const;

	virtual const BF & getSymbolByNameID(const std::string & aNameID,
			avm_type_specifier_kind_t typeFamily) const;


	virtual const BF & getymbolByAstElement(const ObjectElement * astElement,
			avm_type_specifier_kind_t typeFamily) const;


	/**
	 * GETTER - SETTER
	 * mCommunicationCode
	 */
	inline BF & getCommunicationCode()
	{
		return( mCommunicationCode );
	}

	inline const BF & getCommunicationCode() const
	{
		return( mCommunicationCode );
	}

	inline bool hasCommunicationCode() const
	{
		return( mCommunicationCode.valid() );
	}

	inline void setCommunicationCode(const BF & comCode)
	{
		mCommunicationCode = comCode;
	}


	/**
	 * GETTER - SETTER
	 * mInternalCommunicationCode
	 */
	inline BF & getInternalCommunicationCode()
	{
		return( mInternalCommunicationCode );
	}

	inline const BF & getInternalCommunicationCode() const
	{
		return( mInternalCommunicationCode );
	}

	inline bool hasInternalCommunicationCode() const
	{
		return( mInternalCommunicationCode.valid() );
	}

	inline void setInternalCommunicationCode(const BF & comCode)
	{
		mInternalCommunicationCode = comCode;
	}


	/**
	 * GETTER - SETTER
	 * mInputCom
	 */
	inline void addInputCom(InstanceOfPort * aPort)
	{
		mInputCom.add_union( aPort );
	}

	inline void addInputCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputCom.add_union( inputEnabledPort );
	}


	inline ListOfInstanceOfPort & getInputCom()
	{
		return( mInputCom );
	}

	inline const ListOfInstanceOfPort & getInputCom() const
	{
		return( mInputCom );
	}


	bool containsInputCom(InstanceOfPort * aPort) const
	{
		return( mInputCom.contains(aPort) );
	}

	inline bool hasInputCom() const
	{
		return( mInputCom.nonempty() );
	}


	inline void setInputCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputCom.clear();

		mInputCom.add_union( inputEnabledPort );
	}


	/**
	 * GETTER - SETTER
	 * mOutputCom
	 */
	inline void addOutputCom(InstanceOfPort * aPort)
	{
		mOutputCom.add_union( aPort );
	}

	inline void addOutputCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mOutputCom.add_union( inputEnabledPort );
	}


	inline ListOfInstanceOfPort & getOutputCom()
	{
		return( mOutputCom );
	}

	inline const ListOfInstanceOfPort & getOutputCom() const
	{
		return( mOutputCom );
	}


	bool containsOutputCom(InstanceOfPort * aPort) const
	{
		return( mOutputCom.contains(aPort) );
	}

	inline bool hasOutputCom() const
	{
		return( mOutputCom.nonempty() );
	}


	inline void setOutputCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mOutputCom.clear();

		mOutputCom.add_union( inputEnabledPort );
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledBuffer
	 */
	inline void addInputEnabledBuffer(InstanceOfBuffer * aBuffer)
	{
		mInputEnabledBuffer.add_union( aBuffer );
	}

	inline void addInputEnabledBuffer(ListOfInstanceOfBuffer & inputEnabledBuffer)
	{
		mInputEnabledBuffer.add_union( inputEnabledBuffer );
	}


	inline ListOfInstanceOfBuffer & getInputEnabledBuffer()
	{
		return( mInputEnabledBuffer );
	}

	inline const ListOfInstanceOfBuffer & getInputEnabledBuffer() const
	{
		return( mInputEnabledBuffer );
	}


	bool containsInputEnabledBuffer(InstanceOfBuffer * aBuffer) const
	{
		return( mInputEnabledBuffer.contains(aBuffer) );
	}

	inline bool hasInputEnabledBuffer() const
	{
		return( mInputEnabledBuffer.nonempty() );
	}


	inline void setInputEnabledBuffer(ListOfInstanceOfBuffer & inputEnabledBuffer)
	{
		mInputEnabledBuffer.clear();

		mInputEnabledBuffer.add_union( inputEnabledBuffer );
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledCom
	 */
	inline void addInputEnabledCom(InstanceOfPort * aPort)
	{
		mInputEnabledCom.add_union( aPort );
	}

	inline void addInputEnabledCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputEnabledCom.add_union( inputEnabledPort );
	}


	inline ListOfInstanceOfPort & getInputEnabledCom()
	{
		return( mInputEnabledCom );
	}

	inline const ListOfInstanceOfPort & getInputEnabledCom() const
	{
		return( mInputEnabledCom );
	}


	bool containsInputEnabledCom(InstanceOfPort * aPort) const
	{
		return( mInputEnabledCom.contains(aPort) );
	}

	inline bool hasInputEnabledCom() const
	{
		return( mInputEnabledCom.nonempty() );
	}


	inline void setInputEnabledCom(ListOfInstanceOfPort & inputEnabledPort)
	{
		mInputEnabledCom.clear();

		mInputEnabledCom.add_union( inputEnabledPort );
	}


	/**
	 * GETTER - SETTER
	 * mInputEnabledSave
	 */
	inline void addInputEnabledSave(InstanceOfPort * aPort)
	{
		mInputEnabledSave.add_union( aPort );
	}

	inline void addInputEnabledSave(ListOfInstanceOfPort & inputEnabledSavePort)
	{
		mInputEnabledSave.add_union( inputEnabledSavePort );
	}


	inline ListOfInstanceOfPort & getInputEnabledSave()
	{
		return( mInputEnabledSave );
	}

	inline const ListOfInstanceOfPort & getInputEnabledSave() const
	{
		return( mInputEnabledSave );
	}


	bool containsInputEnabledSave(InstanceOfPort * aPort) const
	{
		return( mInputEnabledSave.contains(aPort) );
	}

	inline bool hasInputEnabledSave() const
	{
		return( mInputEnabledSave.nonempty() );
	}


	inline void setInputEnabledSave(ListOfInstanceOfPort & inputEnabledSavePort)
	{
		mInputEnabledSave.clear();

		mInputEnabledSave.add_union( inputEnabledSavePort );
	}


	/**
	 * GETTER - SETTER
	 * mMutableCommunicationFlag
	 * MOC Attribute for mutable Schedule
	 */
	bool isMutableCommunication() const
	{
		return( mMutableCommunicationFlag );
	}

	void setMutableCommunication(bool isMutableCommunication = true)
	{
		mMutableCommunicationFlag = isMutableCommunication;
	}


	/**
	 * GETTER - SETTER
	 * mEnvironmentCom
	 */
	inline BF & getEnvironmentCom()
	{
		return( mEnvironmentCom );
	}

	inline const BF & getEnvironmentCom() const
	{
		return( mEnvironmentCom );
	}

	inline bool hasEnvironmentCom() const
	{
		return( mEnvironmentCom.valid() );
	}

	inline void setEnvironmentCom(const BF & comCode)
	{
		mEnvironmentCom = comCode;
	}


	/**
	 * GETTER - SETTER
	 * mEnvironmentInputCom
	 */
	inline BF & getEnvironmentInputCom()
	{
		return( mEnvironmentInputCom );
	}

	inline const BF & getEnvironmentInputCom() const
	{
		return( mEnvironmentInputCom );
	}

	inline bool hasEnvironmentInputCom() const
	{
		return( mEnvironmentInputCom.valid() );
	}

	inline void setEnvironmentInputCom(const BF & comCode)
	{
		mEnvironmentInputCom = comCode;
	}


	/**
	 * GETTER - SETTER
	 * mEnvironmentOutputCom
	 */
	inline BF & getEnvironmentOutputCom()
	{
		return( mEnvironmentOutputCom );
	}

	inline const BF & getEnvironmentOutputCom() const
	{
		return( mEnvironmentOutputCom );
	}

	inline bool hasEnvironmentOutputCom() const
	{
		return( mEnvironmentOutputCom.valid() );
	}

	inline void setEnvironmentOutputCom(const BF & comCode)
	{
		mEnvironmentOutputCom = comCode;
	}


	/**
	 * Serialization
	 */
	virtual void strHeader(OutStream & out) const;

	void toStreamData(OutStream & out) const;

	void toStreamStaticCom(OutStream & out) const;

	virtual void toStream(OutStream & out) const;

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AvmProgram
// TYPE DEFINITION for TABLE , SMART POINTER and CONTAINER
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class TableOfAvmProgram :
		public TableOfBF_T< AvmProgram >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfAvmProgram )
{

	AVM_DECLARE_CLONABLE_CLASS( TableOfAvmProgram )


/**
 * TYPEDEF
 */
typedef  TableOfBF_T< AvmProgram >  BaseTableOfAvmProgram;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfAvmProgram()
	: BaseTableOfAvmProgram()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfAvmProgram(const TableOfAvmProgram & aTable)
	: BaseTableOfAvmProgram( aTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfAvmProgram()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * For Instance
	 */
	inline const BF & getByQualifiedNameID(
			const std::string & aQualifiedNameID,
			NamedElement::op_comparer_t op,
			Specifier::SCOPE_KIND aScope) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			if( itProg->isScope(aScope)
				&& static_cast< AvmProgram *>(
						itProg )->compareID(aQualifiedNameID, op) )
			{
				return( *itProg );
			}
		}

		return( BF::REF_NULL );
	}

	inline AvmProgram * rawByQualifiedNameID(
			const std::string & aQualifiedNameID,
			NamedElement::op_comparer_t op,
			Specifier::SCOPE_KIND aScope) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			if( itProg->isScope(aScope)
				&& static_cast< AvmProgram *>(
						itProg )->compareID(aQualifiedNameID, op) )
			{
				return( itProg );
			}
		}

		return( NULL );
	}



	inline const BF & getByFQNameID(const std::string & aFullyQualifiedNameID,
		Specifier::SCOPE_KIND aScope = Specifier::SCOPE_UNDEFINED_KIND) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			// STRICT:> compare LOCATOR & LOCATION (true:- retry only LOCATION)
			if( itProg->isScope(aScope)
				&& itProg->fqnEquals( aFullyQualifiedNameID , true ) )
			{
				return( *itProg );
			}
		}

		return( BF::REF_NULL );
	}

	inline const BF & getByQualifiedNameID(
			const std::string & aQualifiedNameID,
			Specifier::SCOPE_KIND aScope =
					Specifier::SCOPE_UNDEFINED_KIND) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			if( itProg->isScope(aScope)
				&& itProg->fqnEndsWith(aQualifiedNameID) )
			{
				return( *itProg );
			}
		}

		return( BF::REF_NULL );
	}


	inline avm_size_t getByQualifiedNameID(
			const std::string & aQualifiedNameID,
			Specifier::SCOPE_KIND aScope, BFList & listofProgram) const
	{
		avm_size_t count = 0;

		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			if( itProg->isScope(aScope)
				&& itProg->fqnEndsWith(aQualifiedNameID) )
			{
				listofProgram.append( *itProg );

				++count;
			}
		}

		return( count );
	}

	inline const BF & getByNameID(const std::string & id,
			Specifier::SCOPE_KIND aScope =
					Specifier::SCOPE_UNDEFINED_KIND) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			if( itProg->isScope(aScope) && (itProg->getNameID() == id) )
			{
				return( *itProg );
			}
		}

		return( BF::REF_NULL );
	}


	inline const BF & getByAstElement(const ObjectElement * astElement) const
	{
		BaseTableOfAvmProgram::const_raw_iterator it = begin();
		BaseTableOfAvmProgram::const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (it)->isAstElement( astElement ) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}


	/**
	 * Serialization
	 */
	inline virtual void toStream(OutStream & os) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			itProg->toStream(os);
			os << EOL;
		}
	}

	inline virtual void fqnStream(OutStream & os) const
	{
		BaseTableOfAvmProgram::const_raw_iterator itProg = begin();
		BaseTableOfAvmProgram::const_raw_iterator endProg = end();
		for( ; itProg != endProg ; ++itProg )
		{
			os << TAB << itProg->getFullyQualifiedNameID() << ";" << EOL;
		}
	}

};


}

#endif /*AVMPROGRAM_H_*/
