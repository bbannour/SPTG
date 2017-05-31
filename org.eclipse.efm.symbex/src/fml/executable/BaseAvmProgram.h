/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 oct. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASEAVMPROGRAM_H_
#define BASEAVMPROGRAM_H_

#include <fml/executable/BaseCompiledForm.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/lib/AvmAnalysis.h>
#include <fml/lib/ITypeSpecifier.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{

class AvmProgram;
class ExecutableForm;
class ObjectElement;


class BaseAvmProgram :
		public BaseCompiledForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BaseAvmProgram )
{

public:
	/**
	 * TYPEDEF
	 */
	typedef avm_uint8_t            TFLAG;

	enum
	{
		EXECUTABLE_UNDEFINED_FLAG  = 0x00,

		EXECUTABLE_COMPILED_FLAG   = 0x01,

		EXECUTABLE_OPTIMIZED_FLAG  = 0x02,

		EXECUTABLE_FINALIZED_FLAG  = EXECUTABLE_COMPILED_FLAG
		                           | EXECUTABLE_OPTIMIZED_FLAG
	};


protected:
	/*
	 * ATTRIBUTES
	 */
	TFLAG mFlag;

	TableOfInstanceOfData mData;

	TableOfInstanceOfData * mBasicData;
	TableOfInstanceOfData * mAllData;


	TableOfInstanceOfData mDataAlias;

	// Static Analysis Data
	// The list of reachable machine per machine
	STATIC_ANALYSIS::VARIABLE_DEPENDENCY_RING mVariableDependencyFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseAvmProgram(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement * astProgram, avm_size_t aSize)
	: BaseCompiledForm(aClassKind, aContainer, astProgram),
	mFlag( EXECUTABLE_UNDEFINED_FLAG ),

	mData( aSize ),
	mBasicData( &mData ),
	mAllData( &mData ),
	mDataAlias( ),

	mVariableDependencyFlag( STATIC_ANALYSIS::UNDEFINED_DEPENDENCY )
	{
		// !! NOTHING
	}

	BaseAvmProgram(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const std::string & aNameID, avm_size_t aSize)
	: BaseCompiledForm(aClassKind, aContainer, aNameID),
	mFlag( EXECUTABLE_UNDEFINED_FLAG ),

	mData( aSize ),
	mBasicData( &mData ),
	mAllData( &mData ),
	mDataAlias( ),

	mVariableDependencyFlag( STATIC_ANALYSIS::UNDEFINED_DEPENDENCY )
	{
		// !! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BaseAvmProgram(const BaseAvmProgram & aProgram)
	: BaseCompiledForm( aProgram ),
	mFlag( aProgram.mFlag ),

	mData( aProgram.mData ),

	mBasicData( (aProgram.mBasicData == &(aProgram.mData) )
			? &mData : aProgram.mBasicData ),

	mAllData( (aProgram.mAllData == &(aProgram.mData) )
			? &mData : aProgram.mAllData ),
	mDataAlias( aProgram.mDataAlias ),

	mVariableDependencyFlag( aProgram.mVariableDependencyFlag )
	{
		// !! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseAvmProgram()
	{
		if( mBasicData != &mData )
		{
			sep::destroy( mBasicData );
		}

		if( mAllData != &mData )
		{
			sep::destroy( mAllData );
		}
	}


	/**
	 * GETTER
	 * mContainer
	 */
	inline BaseAvmProgram * getContainer() const
	{
		return( static_cast< BaseAvmProgram * >( mContainer ) );
	}

	/**
	 * GETTER
	 * For AvmProgram - ExecutableForm Container
	 */
	const AvmProgram * getAvmProgramContainer() const;
	const AvmProgram * getAvmProgram() const;

	ExecutableForm * getExecutableContainer() const;
	ExecutableForm * getExecutable() const;

	inline bool isAncestor(BaseAvmProgram * omrProg)
	{
		BaseAvmProgram * aProg = getContainer();
		for( ; aProg != NULL ; aProg = aProg->getContainer() )
		{
			if( aProg == omrProg )
			{
				return( true );
			}
		}
		return( false );
	}


	/**
	 * GETTER - SETTER
	 * mFlag
	 */
	bool isCompiledFlag()
	{
		return( (mFlag & EXECUTABLE_COMPILED_FLAG) != 0 );
	}

	void setCompiledFlag()
	{
		mFlag = mFlag | EXECUTABLE_COMPILED_FLAG;
	}


	bool isOptimizedFlag()
	{
		return( (mFlag & EXECUTABLE_OPTIMIZED_FLAG) != 0 );
	}

	void setOptimizedFlag()
	{
		mFlag = mFlag | EXECUTABLE_OPTIMIZED_FLAG;
	}


	bool isFinalizedFlag()
	{
		return( (mFlag & EXECUTABLE_FINALIZED_FLAG) != 0 );
	}


	/**
	 * Initialize
	 */
	inline void init(BaseAvmProgram * aContainer, avm_size_t aSize)
	{
		setContainer( aContainer );

		mData.resize(aSize);

		mBasicData = &mData;
		mAllData = &mData;
	}


	/*
	 * contains DATA
	 */
	inline bool containsData(InstanceOfData * anInstance) const
	{
		return( mData.contains(anInstance) ||
				mDataAlias.contains(anInstance) );
	}

	inline bool containsData(const BF & anInstance) const
	{
		return( mData.contains(anInstance) ||
				mDataAlias.contains(anInstance) );
	}


	inline bool containsAllData(InstanceOfData * anInstance) const
	{
		return( mAllData->contains(anInstance) ||
				mDataAlias.contains(anInstance) );
	}

//	inline bool containsAllData(const BF & anInstance) const
//	{
//		return( mAllData->contains(anInstance) ||
//				mDataAlias.contains(anInstance) );
//	}


	/**
	 * GETTER - SETTER
	 * mData
	 */
	inline const BF & saveData(InstanceOfData * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		return( mData.save(anInstance) );
	}

	inline void appendData(const BFList & dataList)
	{
		mData.append( dataList );
	}

	inline void appendData(const BFVector & dataList)
	{
		mData.append( dataList );
	}


	inline const TableOfInstanceOfData & getData() const
	{
		return( mData );
	}


	inline avm_size_t getDataSize() const
	{
		return( mData.size() );
	}


	inline bool hasData() const
	{
		return( mData.nonempty() );
	}


	inline void setData(avm_offset_t offset, InstanceOfData * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance->setContainer(this);

		mData.set(offset, anInstance);
	}

	inline void setData(avm_offset_t offset, const BF & anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		anInstance.to_ptr< InstanceOfData >()->setContainer(this);

		mData.set(offset, anInstance);
	}


	inline void setData(TableOfInstanceOfData & tableOfData)
	{
		resetData( tableOfData );

		updateDataTable();
	}

	inline void resetData(TableOfInstanceOfData & tableOfData)
	{
//		mData.realloc( tableOfData );

		mData.clear();
		mData.append( tableOfData );
	}


	/**
	 * GETTER - SETTER
	 * mBasicData
	 */
	inline const TableOfInstanceOfData & getBasicData() const
	{
		return( * mBasicData );
	}

	inline avm_size_t getBasicDataSize() const
	{
		return( getBasicData().size() );
	}

	inline bool hasBasicData() const
	{
		return( (mBasicData != NULL) && mBasicData->nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mAllData
	 */
	inline const TableOfInstanceOfData & getAllData() const
	{
		return( * mAllData );
	}

	inline avm_size_t getAllDataSize() const
	{
		return( (mAllData != NULL) ? mAllData->size() : 0 );
	}

	inline bool hasAllData() const
	{
		return( (mAllData != NULL) && mAllData->nonempty() );
	}


	/**
	 * UPDATE DATA TABLE
	 * mBasicData
	 * mallData
	 */
	void updateDataTable();

	void collectAllData(TableOfInstanceOfData & tableofAllData,
			TableOfInstanceOfData & tableofBasicData, InstanceOfData * mainInstance,
			TableOfSymbol & relativeDataPath, InstanceOfData * anInstance);


	/**
	 * GETTER - SETTER
	 * mDataAlias
	 */

	inline void appendDataAlias(const Symbol & anAlias)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anAlias )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		mDataAlias.append(anAlias);
	}

	inline const BF & saveDataAlias(InstanceOfData * anInstance)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anInstance )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		return( mDataAlias.save(anInstance) );
	}

	inline const TableOfInstanceOfData & getDataAlias() const
	{
		return( mDataAlias );
	}


	bool hasDataAlias() const
	{
		return( mDataAlias.nonempty() );
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


	virtual const BF & getSymbolByAstElement(
			const ObjectElement * astElement,
			avm_type_specifier_kind_t typeFamily) const;


	/**
	 * GETTER
	 * any SYMBOL filtering by an optional type specifier family
	 * recursively in container
	 */
	inline const BF & getSemSymbol(
			const std::string & aFullyQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const
	{
		const BaseAvmProgram * aProgram = this;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol =
					aProgram->getSymbol(aFullyQualifiedNameID, typeFamily);
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}

		return( BF::REF_NULL );
	}


	inline const BF & getSemSymbolByQualifiedNameID(
			const std::string & aQualifiedNameID,
			avm_type_specifier_kind_t typeFamily) const
	{
		const BaseAvmProgram * aProgram = this;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol = aProgram->
					getSymbolByQualifiedNameID(aQualifiedNameID, typeFamily);
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}

		return( BF::REF_NULL );
	}


	inline const BF & getSemSymbolByNameID(const std::string & aNameID,
			avm_type_specifier_kind_t typeFamily) const
	{
		const BaseAvmProgram * aProgram = this;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol =
					aProgram->getSymbolByNameID(aNameID, typeFamily);
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}

		return( BF::REF_NULL );
	}


	inline const BF & getymbolByAstElement(
			const ObjectElement * astElement,
			avm_type_specifier_kind_t typeFamily) const
	{
		const BaseAvmProgram * aProgram = this;
		for( ; aProgram != NULL ; aProgram = aProgram->getContainer() )
		{
			const BF & theSymbol =
					aProgram->getSymbolByAstElement(astElement, typeFamily);
			if( theSymbol.valid() )
			{
				return( theSymbol );
			}
		}

		return( BF::REF_NULL );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// STATIC ANALYSIS ATTRIBUTE
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * mVariableDependencyFlag
	 */

	STATIC_ANALYSIS::VARIABLE_DEPENDENCY_RING getVariableDependent() const
	{
		return( mVariableDependencyFlag );
	}

	bool isVariableDependent() const
	{
		return( mVariableDependencyFlag == STATIC_ANALYSIS::DEPENDENT );
	}

	bool isVariableIndependent() const
	{
		return( mVariableDependencyFlag == STATIC_ANALYSIS::INDEPENDENT );
	}

	bool hasVariableDependency() const
	{
		return( mVariableDependencyFlag != STATIC_ANALYSIS::UNDEFINED_DEPENDENCY );
	}


	void setVariableDependent(bool isDependent = true)
	{
		mVariableDependencyFlag = ( isDependent ?
				STATIC_ANALYSIS::DEPENDENT : STATIC_ANALYSIS::INDEPENDENT );
	}

	void setVariableDependent()
	{
		mVariableDependencyFlag = STATIC_ANALYSIS::DEPENDENT;
	}

	void setVariableIndependent()
	{
		mVariableDependencyFlag = STATIC_ANALYSIS::INDEPENDENT;
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const;

	virtual void toFscn(OutStream & os) const
	{
		toStream(os);
	}

};


}

#endif /* BASEAVMPROGRAM_H_ */
