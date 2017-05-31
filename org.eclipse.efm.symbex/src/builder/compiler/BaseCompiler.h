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
#ifndef BUILDER_COMPILER_BASECOMPILER_H_
#define BUILDER_COMPILER_BASECOMPILER_H_

#include <common/AvmObject.h>

#include <builder/compiler/BaseCompilerTable.h>

#include <builder/primitive/AvmcodeCompiler.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{

class AvmcodeCompiler;
class AvmProgram;

class BaseCompilerTable;
class BF;

class Configuration;

class DataType;

class ExecutableSystem;

class SymbolTable;


class BaseCompiler  :  public AvmObject
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Configuration & mConfiguration;

public:
	/**
	 * ATTRIBUTE
	 */
	AvmcodeCompiler & mAvmcodeCompiler;

	BaseCompilerTable & mCompilerTable;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseCompiler(Configuration & aConfiguration,
			AvmcodeCompiler & anAvmcodeCompiler)
	: AvmObject( ),
	mConfiguration( aConfiguration ),
	mAvmcodeCompiler( anAvmcodeCompiler ),
	mCompilerTable( anAvmcodeCompiler.mCompilerTable )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Other
	 */
	BaseCompiler(BaseCompiler & aBaseCompiler)
	: AvmObject( ),
	mConfiguration( aBaseCompiler.mConfiguration ),
	mAvmcodeCompiler( aBaseCompiler.mAvmcodeCompiler ),
	mCompilerTable( aBaseCompiler.mCompilerTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseCompiler()
	{
		//!! NOTHING
	}


	/*
	 * GETTER
	 * mConfiguration
	 */
	inline Configuration & getConfiguration()
	{
		return( mConfiguration );
	}


	/*
	 * GETTER
	 * theSymbolTable
	 */
	inline SymbolTable & getSymbolTable()
	{
		return( mCompilerTable.getSymbolTable() );
	}

	/*
	 * GETTER
	 * theErrorCount
	 */
	inline avm_size_t getErrorCount()
	{
		return( mCompilerTable.getErrorCount() );
	}

	inline bool hasError() const
	{
		return( mCompilerTable.hasError() );
	}

	inline bool hasZeroError() const
	{
		return( mCompilerTable.hasZeroError() );
	}

	inline avm_size_t incrErrorCount()
	{
		return( mCompilerTable.incrErrorCount() );
	}


	/*
	 * GETTER
	 * theWarningCount
	 */
	inline avm_size_t getWarningCount()
	{
		return( mCompilerTable.getWarningCount() );
	}

	inline bool hasWarning() const
	{
		return( mCompilerTable.hasWarning() );
	}

	inline bool hasZeroWarning() const
	{
		return( mCompilerTable.hasZeroWarning() );
	}

	inline avm_size_t incrWarningCount()
	{
		return( mCompilerTable.incrWarningCount() );
	}


	/**
	 * REPORT
	 */
	void reportCompilation(OutStream & os) const
	{
		mCompilerTable.reportCompilation(os);
	}


	inline bool hasErrorWarning() const
	{
		return( mCompilerTable.hasError() || mCompilerTable.hasWarning() );
	}

	inline void resetErrorWarning()
	{
		mCompilerTable.resetErrorWarning();
	}


	/**
	 * METHODS
	 * start
	 */
	virtual bool start()
	{
		//!! NOTHING

		return( true );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// TYPE SPECIFIER  [ PRE ] COMPILATION
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	void precompileTypeSpecifier(
			AvmProgram * aContainer, const BF & aDataType);


	TypeSpecifier compileTypeSpecifier(
			AvmProgram * aContainer, const std::string & aTypeID);

	TypeSpecifier compileTypeSpecifier(
			AvmProgram * aContainer, const BF & bfType);

	TypeSpecifier compileStructureSpecifier(
			AvmProgram * aContainer, DataType * aStructureT);

	TypeSpecifier compileChoiceSpecifier(
			AvmProgram * aContainer, DataType * aChoiceT);

	TypeSpecifier compileUnionSpecifier(
			AvmProgram * aContainer, DataType * anUnionT);

	TypeSpecifier compileContainerSpecifier(
			AvmProgram * aContainer, DataType * aCollectionT);

	TypeSpecifier compileIntervalSpecifier(
			AvmProgram * aContainer, DataType * anIntervalT);

	TypeSpecifier compileEnumerationSpecifier(
			AvmProgram * aContainer, DataType * anEnumT);

	TypeSpecifier compileTypeAliasSpecifier(
			AvmProgram * aContainer, DataType * aDataType);




};


}

#endif /* BUILDER_COMPILER_BASECOMPILER_H_ */
