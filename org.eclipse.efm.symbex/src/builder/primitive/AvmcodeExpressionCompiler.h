/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 avr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEEXPRESSIONCOMPILER_H_
#define AVMCODEEXPRESSIONCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS_HEADER("ARITHMETIC_LOGIC_CPU",
		ExpressionALU, AbstractAvmcodeCompiler)

	////////////////////////////////////////////////////////////////////////////
	// UNARY RVALUE COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	inline BFCode compileUnaryRvalue(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, const TypeSpecifier & aType)
	{
		return( StatementConstructor::newCode( aCode->getOperator(),
				compileArgRvalue(aCTX, aType, aCode->first()) ));

	}

	BFCode optimizeUnaryRvalue(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, BaseTypeSpecifier * aType,
			avm_arg_processor_t aProcessor, BaseTypeSpecifier * mainType);


	////////////////////////////////////////////////////////////////////////////
	// BINARY RVALUE COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	inline BFCode compileBinaryRvalue(
			COMPILE_CONTEXT * aCTX, const BFCode & aCode,
			const TypeSpecifier & aType1, const TypeSpecifier & aType2)
	{
		return( StatementConstructor::newCode( aCode->getOperator(),
				compileArgRvalue(aCTX, aType1, aCode->first()),
				compileArgRvalue(aCTX, aType2, aCode->second()) ));
	}

	BFCode optimizeBinaryRvalue(
			COMPILE_CONTEXT * aCTX, const BFCode & aCode,
			BaseTypeSpecifier * aType1, BaseTypeSpecifier * aType2,
			avm_arg_processor_t aProcessor, BaseTypeSpecifier * mainType);


	////////////////////////////////////////////////////////////////////////////
	// ASSOCIATIVE RVALUE COMPILATION STEP
	////////////////////////////////////////////////////////////////////////////

	BFCode compileAssociativeRvalue(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, BaseTypeSpecifier * aType);

	BFCode optimizeAssociativeRvalue(COMPILE_CONTEXT * aCTX,
			const BFCode & aCode, BaseTypeSpecifier * aType,
			avm_arg_processor_t aProcessor, BaseTypeSpecifier * mainType);

};


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("UNARY_ARITHMETIC_LOGIC_CPU",
		UnaryArithmeticExpressionALU, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("BINARY_ARITHMETIC_LOGIC_CPU",
		BinaryArithmeticExpressionALU, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("ASSOCIATIVE_ARITHMETIC_LOGIC_CPU",
		AssociativeArithmeticExpressionALU, AvmcodeExpressionALUCompiler)


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("EXPRESSION#RELATIONAL",
		RelationalExpression, AvmcodeExpressionALUCompiler)


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("UNARY_EXPRESSION#PREDICATE",
		UnaryPredicateExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("BINARY_EXPRESSION#PREDICATE",
		BinaryPredicateExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("ASSOCIATIVE_EXPRESSION#PREDICATE",
		AssociativePredicateExpression, AvmcodeExpressionALUCompiler)


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("UNARY_EXPRESSION#BITWISE",
		UnaryBitwiseExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("BINARY_EXPRESSION#BITWISE",
		BinaryBitwiseExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("ASSOCIATIVE_EXPRESSION#BITWISE",
		AssociativeBitwiseExpression, AvmcodeExpressionALUCompiler)



AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("UNARY_EXPRESSION#STRING",
		UnaryStringExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("BINARY_EXPRESSION#STRING",
		BinaryStringExpression, AvmcodeExpressionALUCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("ASSOCIATIVE_EXPRESSION#STRING",
		AssociativeStringExpression, AvmcodeExpressionALUCompiler)



} /* namespace sep */
#endif /* AVMCODEEXPRESSIONCOMPILER_H_ */
