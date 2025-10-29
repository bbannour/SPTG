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
protected:
	/*
	 * ATTRIBUTES
	 */
	TableOfInstanceOfData mVariables;

	TableOfInstanceOfData * mBasicVariables;
	TableOfInstanceOfData * mAllVariables;

	TableOfInstanceOfData mVariablesAlias;

	// Static Analysis on Variables
	// The list of reachable machine per machine
	STATIC_ANALYSIS::VARIABLE_DEPENDENCY_RING mVariableDependencyFlag;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseAvmProgram(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astProgram, std::size_t aSize)
	: BaseCompiledForm(aClassKind, aContainer, astProgram),
	mVariables( aSize ),
	mBasicVariables( & mVariables ),
	mAllVariables( & mVariables ),
	mVariablesAlias( ),

	mVariableDependencyFlag( STATIC_ANALYSIS::UNDEFINED_DEPENDENCY )
	{
		// !! NOTHING
	}

	BaseAvmProgram(class_kind_t aClassKind, BaseAvmProgram * aContainer,
			const ObjectElement & astProgram,
			const std::string & aNameID, std::size_t aSize)
	: BaseCompiledForm(aClassKind, aContainer, astProgram, aNameID),
	mVariables( aSize ),
	mBasicVariables( & mVariables ),
	mAllVariables( & mVariables ),
	mVariablesAlias( ),

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
	mVariables( aProgram.mVariables ),

	mBasicVariables( (aProgram.mBasicVariables == &(aProgram.mVariables) )
			? &mVariables : aProgram.mBasicVariables ),

	mAllVariables( (aProgram.mAllVariables == &(aProgram.mVariables) )
			? &mVariables : aProgram.mAllVariables ),
	mVariablesAlias( aProgram.mVariablesAlias ),

	mVariableDependencyFlag( aProgram.mVariableDependencyFlag )
	{
		// !! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseAvmProgram()
	{
		if( mBasicVariables != (& mVariables) )
		{
			sep::destroy( mBasicVariables );
		}

		if( mAllVariables != (& mVariables) )
		{
			sep::destroy( mAllVariables );
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

	ExecutableForm & refExecutable() const;

	inline bool isAncestor(BaseAvmProgram * omrProg)
	{
		BaseAvmProgram * aProg = getContainer();
		for( ; aProg != nullptr ; aProg = aProg->getContainer() )
		{
			if( aProg == omrProg )
			{
				return( true );
			}
		}
		return( false );
	}


	/**
	 * Initialize
	 */
	inline void init(BaseAvmProgram * aContainer, std::size_t aSize)
	{
		setContainer( aContainer );

		mVariables.resize(aSize);

		mBasicVariables = (& mVariables);
		mAllVariables = (& mVariables);
	}


	/*
	 * contains DATA
	 */
	inline bool containsVariable(InstanceOfData * aVariable) const
	{
		return( mVariables.contains(aVariable)
				|| mVariablesAlias.contains(aVariable) );
	}

	inline bool containsVariable(const BF & aVariable) const
	{
		return( mVariables.contains(aVariable)
				|| mVariablesAlias.contains(aVariable) );
	}


	inline bool containsAllVariable(InstanceOfData * aVariable) const
	{
		return( mAllVariables->contains(aVariable)
				|| mVariablesAlias.contains(aVariable) );
	}

//	inline bool containsAllVariable(const BF & aVariable) const
//	{
//		return( mAllVariables->contains(aVariable)
//				|| mVariablesAlias.contains(aVariable) );
//	}


	/**
	 * GETTER - SETTER
	 * mVariables
	 */
	inline const BF & saveVariable(InstanceOfData * aVariable)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		aVariable->setContainer(this);

		return( mVariables.save(aVariable) );
	}

	inline void appendVariables(const BFList & variablesList)
	{
		mVariables.append( variablesList );
	}

	inline void appendVariables(const BFVector & variablesList)
	{
		mVariables.append( variablesList );
	}


	inline const TableOfInstanceOfData & getVariables() const
	{
		return( mVariables );
	}

	inline TableOfInstanceOfData & getVariables()
	{
		return( mVariables );
	}


	inline std::size_t getVariablesSize() const
	{
		return( mVariables.size() );
	}


	inline bool hasVariable() const
	{
		return( mVariables.nonempty() );
	}


	inline void setVariable(avm_offset_t offset, InstanceOfData * aVariable)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		aVariable->setContainer(this);

		mVariables.set(offset, aVariable);
	}

	inline void setVariable(avm_offset_t offset, const BF & aVariable)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( aVariable )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		aVariable.to_ptr< InstanceOfData >()->setContainer(this);

		mVariables.set(offset, aVariable);
	}


	inline void setVariables(TableOfInstanceOfData & tableOfVariables)
	{
		resetVariables( tableOfVariables );

		updateVariableTable();
	}

	inline void resetVariables(TableOfInstanceOfData & tableOfVariables)
	{
//		mVariables.realloc( tableOfVariables );

		mVariables.clear();
		mVariables.append( tableOfVariables );
	}


	/**
	 * GETTER - SETTER
	 * mBasicVariables
	 */
	inline const TableOfInstanceOfData & getBasicVariables() const
	{
		return( * mBasicVariables );
	}

	inline std::size_t getBasicVariablesSize() const
	{
		return( getBasicVariables().size() );
	}

	inline bool hasBasicVariable() const
	{
		return( (mBasicVariables != nullptr) && mBasicVariables->nonempty() );
	}


	/**
	 * GETTER - SETTER
	 * mAllVariables
	 */
	inline const TableOfInstanceOfData & getAllVariables() const
	{
		return( * mAllVariables );
	}

	inline TableOfInstanceOfData & getAllVariables()
	{
		return( * mAllVariables );
	}

	inline std::size_t getAllVariablesSize() const
	{
		return( (mAllVariables != nullptr) ? mAllVariables->size() : 0 );
	}

	inline bool hasAllVariable() const
	{
		return( (mAllVariables != nullptr) && mAllVariables->nonempty() );
	}


	/**
	 * UPDATE DATA TABLE
	 * mBasicVariables
	 * mallVariables
	 */
	void updateVariableTable();

	void collectAllVariables(TableOfInstanceOfData & tableofAllVariables,
			TableOfInstanceOfData & tableofBasicVariables,
			InstanceOfData * mainVariableInstance,
			TableOfSymbol & relativeDataPath, InstanceOfData * aVariable);


	/**
	 * GETTER - SETTER
	 * mVariablesAlias
	 */

	inline void appendVariableAlias(const Symbol & anAlias)
	{
		AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anAlias )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		mVariablesAlias.append(anAlias);
	}

	inline const BF & saveVariableAlias(InstanceOfData * aVariable)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( aVariable )
				<< "InstanceOfData !!!"
				<< SEND_EXIT;

		return( mVariablesAlias.save(aVariable) );
	}

	inline const TableOfInstanceOfData & getVariableAlias() const
	{
		return( mVariablesAlias );
	}


	bool hasVariableAlias() const
	{
		return( mVariablesAlias.nonempty() );
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
			const ObjectElement & astElement,
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
		for( ; aProgram != nullptr ; aProgram = aProgram->getContainer() )
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
		for( ; aProgram != nullptr ; aProgram = aProgram->getContainer() )
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
		for( ; aProgram != nullptr ; aProgram = aProgram->getContainer() )
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

//!@?UNUSED:
//	inline const BF & getymbolByAstElement(
//			const ObjectElement & astElement,
//			avm_type_specifier_kind_t typeFamily) const
//	{
//		const BaseAvmProgram * aProgram = this;
//		for( ; aProgram != nullptr ; aProgram = aProgram->getContainer() )
//		{
//			const BF & theSymbol =
//					aProgram->getSymbolByAstElement(astElement, typeFamily);
//			if( theSymbol.valid() )
//			{
//				return( theSymbol );
//			}
//		}
//
//		return( BF::REF_NULL );
//	}


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
	virtual void toStream(OutStream & os) const override;

	virtual void toFscn(OutStream & os) const
	{
		toStream(os);
	}

};


}

#endif /* BASEAVMPROGRAM_H_ */
