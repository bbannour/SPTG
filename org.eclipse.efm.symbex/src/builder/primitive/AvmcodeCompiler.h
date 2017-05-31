/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODECOMPILER_H_
#define AVMCODECOMPILER_H_

#include <vector>

#include <common/AvmObject.h>
#include <common/BF.h>

#include <builder/primitive/CompilationEnvironment.h>

#include <collection/Typedef.h>

#include <fml/expression/AvmCode.h>

#include <fml/symbol/Symbol.h>


namespace sep
{


class AbstractAvmcodeCompiler;
class AvmcodeUfiExpressionCompiler;

class BaseCompiler;
class BaseCompilerTable;

class ArrayBF;
class ArrayIdentifier;
class ArrayQualifiedIdentifier;

class AvmCode;
class AvmProgram;

class Configuration;

class Element;
class ExecutableForm;
class ExecutableSystem;

class Routine;
class SymbolTable;
class TypeSpecifier;

class UniFormIdentifier;


class AvmcodeCompiler  :  public AvmObject
{

public:
	/**
	 * ATTRIBUTE
	 */
	Configuration & mConfiguration;

	BaseCompilerTable & mCompilerTable;


	AvmcodeUfiExpressionCompiler * UFI_EXPRESSION_COMPILER;

	std::vector< AbstractAvmcodeCompiler * >  AVMCODE_COMPILER_TABLE;
	std::vector< AbstractAvmcodeCompiler * >  AVMCODE_COMPILER_TABLE_FOR_DESTROY;

	AbstractAvmcodeCompiler * DEFAULT_AVMCODE_COMPILER;
	AbstractAvmcodeCompiler * NOTHING_AVMCODE_COMPILER;

	AbstractAvmcodeCompiler * UNARY_ARITHMETIC_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * BINARY_ARITHMETIC_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * UNARY_BITWISE_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * BINARY_BITWISE_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * ASSOCIATIVE_BITWISE_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * UNARY_PREDICATE_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * BINARY_PREDICATE_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * RELATIONAL_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * UNARY_STRING_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * BINARY_STRING_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * ASSOCIATIVE_STRING_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * LOOKUP_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * MACHINE_STATUS_EXPRESSION_COMPILER;
	AbstractAvmcodeCompiler * MATH_FUNCTION_COMPILER;
	AbstractAvmcodeCompiler * VARIABLE_STATUS_EXPRESSION_COMPILER;

	AbstractAvmcodeCompiler * ACTIVITY_STATEMENT_COMPILER;
	AbstractAvmcodeCompiler * SCHEDULING_STATEMENT_COMPILER;
	AbstractAvmcodeCompiler * SEQUENCE_STATEMENT_COMPILER;

	AbstractAvmcodeCompiler * ITE_STATEMENT_COMPILER;

	AbstractAvmcodeCompiler * UNARY_CONTAINER_STATEMENT;
	AbstractAvmcodeCompiler * UNARY_WRITE_CONTAINER_STATEMENT;

	AbstractAvmcodeCompiler * BINARY_CONTAINER_STATEMENT;
	AbstractAvmcodeCompiler * BINARY_WRITE_CONTAINER_STATEMENT;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmcodeCompiler(Configuration & aConfiguration,
			BaseCompilerTable & aCompilerTable)
	: AvmObject( ),
	mConfiguration( aConfiguration ),
	mCompilerTable( aCompilerTable ),

	UFI_EXPRESSION_COMPILER( NULL ),

	AVMCODE_COMPILER_TABLE( ),
	AVMCODE_COMPILER_TABLE_FOR_DESTROY( ),

	DEFAULT_AVMCODE_COMPILER( NULL ),
	NOTHING_AVMCODE_COMPILER( NULL ),

	UNARY_ARITHMETIC_EXPRESSION_COMPILER( NULL ),
	BINARY_ARITHMETIC_EXPRESSION_COMPILER( NULL ),
	ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER( NULL ),

	UNARY_BITWISE_EXPRESSION_COMPILER( NULL ),
	BINARY_BITWISE_EXPRESSION_COMPILER( NULL ),
	ASSOCIATIVE_BITWISE_EXPRESSION_COMPILER( NULL ),

	UNARY_PREDICATE_EXPRESSION_COMPILER( NULL ),
	BINARY_PREDICATE_EXPRESSION_COMPILER( NULL ),
	ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER( NULL ),

	RELATIONAL_EXPRESSION_COMPILER( NULL ),

	UNARY_STRING_EXPRESSION_COMPILER( NULL ),
	BINARY_STRING_EXPRESSION_COMPILER( NULL ),
	ASSOCIATIVE_STRING_EXPRESSION_COMPILER( NULL ),

	LOOKUP_EXPRESSION_COMPILER( NULL ),
	MACHINE_STATUS_EXPRESSION_COMPILER( NULL ),
	MATH_FUNCTION_COMPILER( NULL ),
	VARIABLE_STATUS_EXPRESSION_COMPILER( NULL ),

	ACTIVITY_STATEMENT_COMPILER( NULL ),
	SCHEDULING_STATEMENT_COMPILER( NULL ),
	SEQUENCE_STATEMENT_COMPILER( NULL ),
	ITE_STATEMENT_COMPILER( NULL ),

	UNARY_CONTAINER_STATEMENT( NULL ),
	UNARY_WRITE_CONTAINER_STATEMENT( NULL ),

	BINARY_CONTAINER_STATEMENT( NULL ),
	BINARY_WRITE_CONTAINER_STATEMENT( NULL )
	{
			//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmcodeCompiler();


	/**
	 * GETTER
	 * mConfiguration
	 */
	inline Configuration & getConfiguration() const
	{
		return( mConfiguration );
	}

	/*
	 * GETTER
	 * mCompilerTable
	 */
	inline BaseCompilerTable & getCompilerTable()
	{
		return( mCompilerTable );
	}

	/*
	 * GETTER
	 * theSymbolTable
	 */
	SymbolTable & getSymbolTable();


	/**
	 * CONFIGURE
	 */
	bool configure();

	bool configureOther();

	bool configureMeta();

	bool configureLambdaPrimitive();

	bool configureActivityPrimitive();

	bool configureStatusPrimitive();

	bool configureSchedulingPrimitive();
	bool configureBasicPrimitive();

	bool configureArithmeticPrimitive();
	bool configureBitwisePrimitive();
	bool configureLogicPrimitive();

	bool configureLookupPrimitive();
	bool configureMathematicPrimitive();

	bool configureStringCollectionPrimitive();

	bool configureIoltPrimitive();


	/*
	 * COMPILE  ARGUMENT
	 */
	const BF & postCompileSymbol(const BF & aSymbol);

	BF compileUFI(COMPILE_CONTEXT * aCTX, const UniFormIdentifier & anUFI);


	BF compileFullyQualifiedNameID(COMPILE_CONTEXT * aCTX,
			const std::string & aFullyQualifiedNameID);

	inline BF compileFullyQualifiedNameID(
			COMPILE_CONTEXT * aCTX, const BF & aFQN_ID)
	{
		return( compileFullyQualifiedNameID(aCTX, aFQN_ID.str()) );
	}


	BF compileQualifiedIdentifier(
			COMPILE_CONTEXT * aCTX, const BF & aQualifiedNameID);

	BF compileQualifiedPositionalIdentifier(
			COMPILE_CONTEXT * aCTX, const BF & aQualifiedNameID);


	BF compileIdentifier(COMPILE_CONTEXT * aCTX, const std::string & aNameID);

	inline BF compileIdentifier(COMPILE_CONTEXT * aCTX, const BF & aNameID)
	{
		return( compileIdentifier(aCTX, aNameID.str()) );
	}


	const BF & compileElement(COMPILE_CONTEXT * aCTX, const BF & anElement);

	const BF & compileDataType(COMPILE_CONTEXT * aCTX, const BF & aDataType);
	const BF & compileVariable(COMPILE_CONTEXT * aCTX, const BF & aVariable);
	const BF & compileBuffer(COMPILE_CONTEXT * aCTX, const BF & aBuffer);
	const BF & compilePort(COMPILE_CONTEXT * aCTX, const BF & aPort);
	const BF & compileConnector(COMPILE_CONTEXT * aCTX, const BF & aConnector);

	const BF & compileMachine(COMPILE_CONTEXT * aCTX, const BF & aMachine);
	const BF & compileRoutine(COMPILE_CONTEXT * aCTX, const BF & aRoutine);
	const BF & compileTransition(COMPILE_CONTEXT * aCTX, const BF & aTransition);


	/*
	 * DECODE & COMPILE  EXPRESSION
	 */
	BF decode_compileExpression(COMPILE_CONTEXT * aCTX, const BF & aCode);

	BF decode_compileExpression(AvmProgram * aCompileCtx, const BF & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( decode_compileExpression(compilENV.mCTX, aCode) );
	}

	BF compileArrayOfIdentifier(COMPILE_CONTEXT * aCTX, ArrayIdentifier * idArray);

	BF compileArrayOfQualifiedIdentifier(COMPILE_CONTEXT * aCTX,
			ArrayQualifiedIdentifier * ufiArray);

	BF compileArrayOfBF(COMPILE_CONTEXT * aCTX, ArrayBF * bfarray);


	BF compileExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);


	BF decode_optimizeExpression(COMPILE_CONTEXT * aCTX, const BF & aCode);


	BF optimizeExpression(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

	BF optimizeExpression(AvmProgram * aCompileCtx, const BFCode & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( optimizeExpression(compilENV.mCTX, aCode) );
	}


	BF decode_compileVariableMachine(COMPILE_CONTEXT * aCTX, const BF & aCode);

	BF decode_compileVariablePort(COMPILE_CONTEXT * aCTX, const BF & aCode);

	BF decode_compileVariableBuffer(COMPILE_CONTEXT * aCTX, const BF & aCode);


	/*
	 * DECODE & COMPILE  EXPRESSION
	 */
	bool optimizeEvalExpression(COMPILE_CONTEXT * aCTX, BFCode & aCode);

	bool optimizeEvalExpression(AvmProgram * aCompileCtx, BFCode & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( optimizeEvalExpression(compilENV.mCTX, aCode) );
	}


	/*
	 * DECODE & COMPILE  STATEMENT
	 */
	BF decode_compileStatement(COMPILE_CONTEXT * aCTX, const BF & aCode);

	BF decode_compileStatement(AvmProgram * aCompileCtx, const BF & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( decode_compileStatement(compilENV.mCTX, aCode) );
	}


	BFCode compileStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

	BFCode compileStatement(AvmProgram * aCompileCtx, const BFCode & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( compileStatement(compilENV.mCTX, aCode) );
	}


	BF decode_optimizeStatement(COMPILE_CONTEXT * aCTX, const BF & aCode);

	BF decode_optimizeStatement(AvmProgram * aCompileCtx, const BF & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( decode_optimizeStatement(compilENV.mCTX, aCode) );
	}


	BFCode optimizeStatement(COMPILE_CONTEXT * aCTX, const BFCode & aCode);

	BFCode optimizeStatement(AvmProgram * aCompileCtx, const BFCode & aCode)
	{
		CompilationEnvironment compilENV(aCompileCtx);

		return( optimizeStatement(compilENV.mCTX, aCode) );
	}


	AvmProgram * compileRoutineStructure(BaseCompiler * aCompiler,
			AvmProgram * aProgramCtx, Routine * aRoutine);

	AvmProgram * compileRoutine(BaseCompiler * aCompiler,
			AvmProgram * aProgramCtx, Routine * aRoutine);

	AvmProgram * compileRoutine(
			BaseCompiler * aCompiler, AvmProgram * aProgramCtx,
			InstanceOfData * aVarInstanceCtx, Routine * aRoutine);

	AvmProgram * compileRoutine(
			BaseCompiler * aCompiler, AvmProgram * aProgramCtx,
			const TypeSpecifier & aTypeSpecifierCtx, Routine * aRoutine);


	BF substituteUfiByInstance(ExecutableForm * theExecutable,
			const BF & anElement, ListOfSymbol & usingInstance);


	/*
	 * OPTIMIZE PROGRAM from EXECUTABLE or DATA
	 */
	void optimizeProgramRoutine(AvmProgram * aProgram);

	void optimizeDataRoutine(AvmProgram * aProgram);

	void optimizeDataRoutine(ExecutableForm * theExecutable);

	void optimizeInstance(ExecutableForm * theExecutableContainer,
			InstanceOfMachine * aMachine);

};


}

#endif /* AVMCODECOMPILER_H_ */
