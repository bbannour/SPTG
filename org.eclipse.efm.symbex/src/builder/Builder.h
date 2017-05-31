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
#ifndef BUILDER_H_
#define BUILDER_H_

#include <computer/EvaluationEnvironment.h>

#include <builder/compiler/BaseCompilerTable.h>

#include <builder/compiler/Compiler.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{

class AvmCode;
class AvmcodeCompiler;
class AvmPrimitiveProcessor;
class AvmProgram;

class Configuration;

class ExecutionData;
class ExecutableSystem;

class ObjectElement;

class SymbexEngine;

class UniFormIdentifier;



class Builder
{

protected:
	/**
	 * ATTRIBUTE
	 */
	SymbexEngine & mSymbexEngine;

	Configuration & mConfiguration;

	EvaluationEnvironment ENV;

	BaseCompilerTable mBaseCompilerTable;

	AvmcodeCompiler mAvmcodeCompiler;

	Compiler mCompiler;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Builder(SymbexEngine & aSymbexEngine, Configuration & aConfiguration,
			AvmPrimitiveProcessor & aPrimitiveProcessor)
	: mSymbexEngine( aSymbexEngine ),
	mConfiguration( aConfiguration ),
	ENV( aPrimitiveProcessor ),
	mBaseCompilerTable( aConfiguration ),
	mAvmcodeCompiler( aConfiguration , mBaseCompilerTable ),
	mCompiler( aConfiguration , mAvmcodeCompiler )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Builder()
	{
		//!! NOTHING
	}


	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * CONFIGURE
	 */
	bool configure();


	/**
	 * GETTER
	 * mConfiguration
	 * mAvmcodeCompiler
	 * mCompiler
	 */
	inline Configuration & getConfiguration()
	{
		return( mConfiguration );
	}

	inline AvmcodeCompiler & getAvmcodeCompiler()
	{
		return( mAvmcodeCompiler );
	}

	inline Compiler & getCompiler()
	{
		return( mCompiler );
	}


	/**
	 * GETTER
	 * Compiler Error / Warning count
	 */
	inline bool hasError()
	{
		return( mCompiler.hasError() );
	}

	inline bool hasWarning()
	{
		return( mCompiler.hasWarning() );
	}


	inline void resetErrorWarning()
	{
		mCompiler.resetErrorWarning();
	}


	/**
	 * START
	 */
	bool start();

	/*
	 * Initial Execution Context creation
	 */
	APExecutionData createInitialExecutionData();


	/**
	 * BUILDER
	 * Replace UFI of var by this associated BaseInstanceForm
	 */

	inline BF compileExpression(ExecutableForm * anExecutable, const BF & aCode)
	{
		CompilationEnvironment compilENV(anExecutable);

		compilENV.mCTX->setModifier(
				Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER );

		BF bf = mAvmcodeCompiler.decode_compileExpression(
				compilENV.mCTX, aCode);

		return( ( bf.isnot< AvmCode >() ) ?  bf  :
			mAvmcodeCompiler.optimizeExpression(compilENV.mCTX, bf.bfCode()) );
	}

	inline BF compileExpression(const BF & aCode);


	inline BFCode compileStatement(
			ExecutableForm * anExecutable, const BFCode & aCode)
	{
		BFCode compiledCode =
				mAvmcodeCompiler.compileStatement(anExecutable, aCode);

		return( mAvmcodeCompiler.optimizeStatement(
				anExecutable, compiledCode) );
	}

	inline BFCode compileStatement(const BFCode & aCode);



	BF build(TableOfSymbol & aliasTable,
			const ExecutionData & anED, const BF & aCode);


	BF build(const ExecutionData & anED, const BF & aCode);

	inline BF build(const APExecutionData & apED, const BF & aCode)
	{
		return( build((* apED), aCode) );
	}


	BF build(TableOfSymbol & aliasTable, const ExecutionData & anED,
			const AvmProgram & aProgram, const BF & aCode);

	BF compile(TableOfSymbol & aliasTable,
			const ExecutionData & anED, const BF & aCode);


	BF searchSymbolInstance(TableOfSymbol & aliasTable,
			const ExecutionData & anED, UniFormIdentifier * anUFI);

	const BF & searchSymbolInstance(TableOfSymbol & aliasTable,
			const ExecutionData & anED, const ObjectElement * objElement);

	const BF & searchSymbolInstance(TableOfSymbol & aliasTable,
			const ExecutionData & anED, const BF & aBaseInstance);

};


} /* namespace sep */

#endif /*BUILDER_H_*/
