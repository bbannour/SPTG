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

#include "AvmcodeExpressionCompiler.h"

#include <fml/executable/InstanceOfData.h>

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/ClassTypeSpecifier.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// UNARY RVALUE COMPILATION STEP
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeExpressionALUCompiler::optimizeUnaryRvalue(COMPILE_CONTEXT * aCTX,
		const BFCode & aCode, const BaseTypeSpecifier & aType,
		avm_arg_processor_t aProcessor, const BaseTypeSpecifier & mainType)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = (& aType);
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first(), false);

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ aProcessor,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ (& mainType) );

	// set operation on string
	if( (argsInstruction->at(0).operand == AVM_ARG_STRING_KIND)
		|| argsInstruction->at(0).dtype->isTypedString() )
	{
		argsInstruction->setMainBytecode(
				/*context  */ AVM_ARG_RETURN_CTX,
				/*processor*/ AVM_ARG_STRING_CPU,
				/*operation*/ AVM_ARG_SEVAL_RVALUE,
				/*operand  */ AVM_ARG_EXPRESSION_KIND,
				/*dtype    */ mainType );
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// BINARY RVALUE COMPILATION STEP
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeExpressionALUCompiler::optimizeBinaryRvalue(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode,
		const BaseTypeSpecifier & aType1, const BaseTypeSpecifier & aType2,
		avm_arg_processor_t aProcessor, const BaseTypeSpecifier & mainType)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = (& aType1);
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first(), false);

	optimizeArgExpression(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = (& aType2);
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second(), false);

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ aProcessor,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ (& mainType) );

	// set operation on string
	if( ((argsInstruction->at(0).operand == AVM_ARG_STRING_KIND)
			|| argsInstruction->at(0).dtype->isTypedString())
		&& ((argsInstruction->at(1).operand == AVM_ARG_STRING_KIND)
			|| argsInstruction->at(1).dtype->isTypedString()) )
	{
		argsInstruction->setMainBytecode(
				/*context  */ AVM_ARG_RETURN_CTX,
				/*processor*/ AVM_ARG_STRING_CPU,
				/*operation*/ AVM_ARG_SEVAL_RVALUE,
				/*operand  */ AVM_ARG_EXPRESSION_KIND,
				/*dtype    */ mainType );
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// ASSOCIATIVE RVALUE COMPILATION STEP
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeExpressionALUCompiler::compileAssociativeRvalue(
	COMPILE_CONTEXT * aCTX, const BFCode & aCode,
	const BaseTypeSpecifier & aType)
{
	const Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;

	aCTX = aCTX->clone(aType);

	for( const auto & itOperand : aCode.getOperands() )
	{
		arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, itOperand);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > compilation error << "
					<< itOperand.str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			const AvmCode & argCode = arg.to< AvmCode >();

			if( argCode.isOperator( mainOperator ) &&
				mainOperator->isAssociative() )
			{
				newCode->append( argCode.getOperands() );
			}
			else
			{
				newCode->append( arg );
			}
		}
		else
		{
			newCode->append( arg );
		}
	}

	return( newCode );
}

BFCode AvmcodeExpressionALUCompiler::optimizeAssociativeRvalue(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode,
		const BaseTypeSpecifier & aType, avm_arg_processor_t aProcessor,
		const BaseTypeSpecifier & mainType)
{
	const Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;

	AvmInstruction * argsInstruction = newCode->newEmptyInstruction();

	Vector< AvmBytecode > vectorOfArgOpcode;

	std::size_t stringArgCount = 0;

	for( const auto & itOperand : aCode.getOperands() )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, itOperand);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > optimization error << "
					<< itOperand.str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			const AvmCode & argCode = arg.to< AvmCode >();

			if( argCode.isOperator( mainOperator ) &&
				mainOperator->isAssociative() )
			{
				newCode->append( argCode.getOperands() );

				vectorOfArgOpcode.append(
						argCode.getInstruction()->getBytecode(), argCode.size());
			}
			else
			{
				newCode->append( arg );

				if( argCode.hasInstruction() )
				{
					vectorOfArgOpcode.append( argcodeOfExpression(aCTX, argCode) );
				}
				else
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected expression without argcode << "
							<< argCode.strDebug() << " >> !!!"
							<< SEND_EXIT;

					vectorOfArgOpcode.append( AvmBytecode(AVM_ARG_ARGUMENT_CTX,
							AVM_ARG_SEVAL_RVALUE, AVM_ARG_EXPRESSION_KIND) );
				}
				vectorOfArgOpcode.back().context = AVM_ARG_ARGUMENT_CTX;
			}
		}
		else
		{
			newCode->append( arg );

			AvmBytecode argOpcode;
			setArgcodeRValue(aCTX, argOpcode, arg, false);
			argOpcode.context = AVM_ARG_ARGUMENT_CTX;
			vectorOfArgOpcode.append( argOpcode );
		}

		if( (vectorOfArgOpcode.back().operand == AVM_ARG_STRING_KIND)
			|| vectorOfArgOpcode.back().dtype->isTypedString() )
		{
			stringArgCount += 1;
		}
	}

	argsInstruction->setMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ aProcessor,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ mainType );

	argsInstruction->computeBytecode( false , vectorOfArgOpcode );

	// set operation on string
	if( stringArgCount > 0 )
	{
		argsInstruction->setMainBytecode(
				/*context  */ AVM_ARG_RETURN_CTX,
				/*processor*/ AVM_ARG_STRING_CPU,
				/*operation*/ AVM_ARG_SEVAL_RVALUE,
				/*operand  */ AVM_ARG_EXPRESSION_KIND,
				/*dtype    */ mainType );
	}

	return( newCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ARITHMETIC LOGIC CPU COMPILATION for UNARY EXPRESSION
////////////////////////////////////////////////////////////////////////////////


BF AvmcodeExpressionALUCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileUnaryRvalue(aCTX, aCode, TypeManager::UNIVERSAL) );
}


BF AvmcodeExpressionALUCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
//	argsInstruction->setMainBytecode(
//			/*context  */ AVM_ARG_RETURN_CTX,
//			/*processor*/ AVM_ARG_ARITHMETIC_LOGIC_CPU,
//			/*operation*/ AVM_ARG_SEVAL_RVALUE,
//			/*operand  */ AVM_ARG_EXPRESSION_KIND,
//			/*dtype    */ argsInstruction->at(0).dtype);

	return( optimizeUnaryRvalue(aCTX, aCode, TypeManager::UNIVERSAL,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::UNIVERSAL) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ARITHMETIC LOGIC CPU COMPILATION for UNARY EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryArithmeticExpressionALUCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileUnaryRvalue(aCTX, aCode, TypeManager::UNIVERSAL) );
}


BF AvmcodeUnaryArithmeticExpressionALUCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
//	argsInstruction->setMainBytecode(
//			/*context  */ AVM_ARG_RETURN_CTX,
//			/*processor*/ AVM_ARG_ARITHMETIC_LOGIC_CPU,
//			/*operation*/ AVM_ARG_SEVAL_RVALUE,
//			/*operand  */ AVM_ARG_EXPRESSION_KIND,
//			/*dtype    */ argsInstruction->at(0).dtype);

	return( optimizeUnaryRvalue(aCTX, aCode, TypeManager::UNIVERSAL,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::UNIVERSAL) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ARITHMETIC LOGIC CPU COMPILATION for BINARY EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryArithmeticExpressionALUCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileBinaryRvalue(aCTX, aCode,
			TypeManager::UNIVERSAL, TypeManager::UNIVERSAL) );
}


BF AvmcodeBinaryArithmeticExpressionALUCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeBinaryRvalue(aCTX, aCode,
			TypeManager::UNIVERSAL, TypeManager::UNIVERSAL,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::UNIVERSAL) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ARITHMETIC LOGIC CPU COMPILATION for ASSOCIATIVE EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAssociativeArithmeticExpressionALUCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileAssociativeRvalue(aCTX, aCode, TypeManager::UNIVERSAL) );
}


BF AvmcodeAssociativeArithmeticExpressionALUCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeAssociativeRvalue(aCTX, aCode, TypeManager::UNIVERSAL,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::UNIVERSAL) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE PREDICAT EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

static void compareStructure(BaseAvmProgram * aProgram,	AvmCode * expandCode,
		const Operator * op, const Symbol & arg1, const Symbol & arg2)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
//	AVM_OS_TRACE << "compareStructure:> " << std::endl;
//	arg1.toStream(AVM_OS_TRACE);
//	arg2.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << "compareStructure:> " << std::endl
			<< "\t" << str_header( arg1 )  << std::endl
			<< "\t" << str_header( arg2 )  << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	if( arg1.hasAttribute() && arg2.hasAttribute() )
	{
		TableOfSymbol::const_iterator it1 = arg1.getAttribute()->begin();
		TableOfSymbol::const_iterator it2 = arg2.getAttribute()->begin();
		TableOfSymbol::const_iterator itEnd = arg1.getAttribute()->end();
		for( ; it1 != itEnd ; ++it1 , ++it2 )
		{
			compareStructure(aProgram, expandCode, op, (*it1) , (*it2));
		}
	}

	else if( arg1.hasAttribute() || arg2.hasAttribute() )
	{
		const Symbol & argAttrs = arg1.hasAttribute() ? arg1 : arg2;
		const Symbol & argOther = arg1.hasDataPath()  ? arg1 : arg2;

		Symbol argAlias;
		std::string aQualifiedNameID;

		TableOfSymbol::const_iterator it = argAttrs.getAttribute()->begin();
		TableOfSymbol::const_iterator itEnd = argAttrs.getAttribute()->end();
		for( ; it != itEnd ; ++it )
		{
			argAlias = new InstanceOfData(argOther.getPointerNature(),
					argOther.getContainer(), argOther.variable(),
					*(argOther.getDataPath()), (*it));

			aQualifiedNameID = (*it).getFullyQualifiedNameID().substr(
					argAttrs.getFullyQualifiedNameID().length() + 1);

			argAlias.updateFullyQualifiedNameID(
					OSS() << argOther.getFullyQualifiedNameID()
							<< '.' << aQualifiedNameID,
					OSS() << argOther.getNameID()  << '.' << aQualifiedNameID );

			aProgram->appendVariableAlias(argAlias);

			compareStructure(aProgram, expandCode, op, (*it) , argAlias);
		}
	}

	else if( arg1.referedTypeSpecifier().isTypedStructure() )
	{
		Symbol arg1Alias;
		Symbol arg2Alias;
		std::string id;

		const ClassTypeSpecifier & structT =
				arg1.referedTypeSpecifier().to< ClassTypeSpecifier >();

		for( const auto & itSymbol : structT.getSymbolData() )
		{
			id = itSymbol.getNameID();

			arg1Alias = new InstanceOfData(arg1.getPointerNature(),
					arg1.getContainer(), arg1.variable(),
					*(arg1.getDataPath()), itSymbol);

			arg1Alias.updateFullyQualifiedNameID(
					( OSS() << arg1.getFullyQualifiedNameID() << '.' << id ),
					( OSS() << arg1.getNameID()  << '.' << id ) );

			aProgram->appendVariableAlias(arg1Alias);


			arg2Alias = new InstanceOfData(arg2.getPointerNature(),
					arg2.getContainer(), arg2.variable(),
					*(arg2.getDataPath()), itSymbol);

			arg2Alias.updateFullyQualifiedNameID(
					( OSS() << arg2.getFullyQualifiedNameID() << '.' << id ),
					( OSS() << arg2.getNameID()  << '.' << id ) );

			aProgram->appendVariableAlias(arg2Alias);

			compareStructure(aProgram, expandCode, op, arg1Alias , arg2Alias);
		}
	}

	else
	{
		BFCode atomCode(op);

		if( arg1.isFieldClassAttributePointer() ||
			arg1.isFieldArrayOffsetPointer() )
		{
			atomCode->append( INCR_BF(
					const_cast< BaseInstanceForm * >(arg1.getAliasTarget()) ));
		}
		else
		{
			atomCode->append( arg1 );
		}

		if( arg2.isFieldClassAttributePointer() ||
			arg2.isFieldArrayOffsetPointer() )
		{
			atomCode->append( INCR_BF(
					const_cast< BaseInstanceForm * >(arg2.getAliasTarget()) ));
		}
		else
		{
			atomCode->append( arg2 );
		}

		expandCode->append( atomCode );
	}
}


static void compareStructure(BaseAvmProgram * aProgram, AvmCode * expandCode,
		const Operator * op, const Symbol & arg1, const BF & arg2)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
//	AVM_OS_TRACE << "compareStructure:> " << std::endl;
//	arg1.toStream(AVM_OS_TRACE);
//	arg2.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << "compareStructure:> " << std::endl
			<< "\t" << str_header( arg1 )  << std::endl
			<< "\t" << arg2.str()  << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )


	if( arg1.hasAttribute() && arg2.is< ArrayBF >())
	{
		ArrayBF * arg2Array = arg2.to_ptr< ArrayBF >();
		std::size_t offset = 0;

		TableOfSymbol::const_iterator it = arg1.getAttribute()->begin();
		TableOfSymbol::const_iterator itEnd = arg1.getAttribute()->end();
		for( ; (it != itEnd) && (offset < arg2Array->size()) ; ++it , ++offset )
		{
			compareStructure(aProgram, expandCode,
					op, (*it), arg2Array->at(offset));
		}
	}

	else if( arg1.referedTypeSpecifier().isTypedStructure()
			&& arg2.is< ArrayBF >() )
	{
		ArrayBF * arg2Array = arg2.to_ptr< ArrayBF >();
		std::size_t offset = 0;

		Symbol arg1Alias;
		std::string id;

		const ClassTypeSpecifier & structT =
				arg1.referedTypeSpecifier().to< ClassTypeSpecifier >();

		TableOfSymbol::const_iterator it = structT.getSymbolData().begin();
		TableOfSymbol::const_iterator itEnd = structT.getSymbolData().end();
		for( ; (it != itEnd) && (offset < arg2Array->size()) ; ++it , ++offset )
		{
			id = (*it).getNameID();

			arg1Alias = new InstanceOfData(arg1.getPointerNature(),
					arg1.getContainer(), arg1.variable(),
					*(arg1.getDataPath()), (*it));

			arg1Alias.updateFullyQualifiedNameID(
					( OSS() << arg1.getFullyQualifiedNameID() << '.' << id ),
					( OSS() << arg1.getNameID()  << '.' << id ) );

			aProgram->appendVariableAlias(arg1Alias);

			compareStructure(aProgram, expandCode, op,
					arg1Alias, arg2Array->at(offset));
		}
	}

	else
	{
		BFCode atomCode(op);

		if( arg1.isFieldClassAttributePointer() ||
			arg1.isFieldArrayOffsetPointer() )
		{
			atomCode->append( INCR_BF(
				const_cast< BaseInstanceForm * >(arg1.getAliasTarget()) ));
		}
		else
		{
			atomCode->append( arg1 );
		}

		atomCode->append( arg2 );

		expandCode->append( atomCode );
	}
}


BF AvmcodeRelationalExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BF compileCode = compileBinaryRvalue(aCTX, aCode,
			TypeManager::UNIVERSAL, TypeManager::UNIVERSAL);

	if( compileCode.is< AvmCode >() )
	{
		const AvmCode & compileAvmCode = compileCode.to< AvmCode >();

		if( compileAvmCode.first().is< InstanceOfData >() )
		{
			Symbol arg1( compileAvmCode.first() );

			if( aCTX->isNeedTypeChecking() )
			{
				checkArgType(aCTX,
						arg1.getTypeSpecifier(),
						compileAvmCode.second());
			}

			const BaseTypeSpecifier & arg1Type = arg1.referedTypeSpecifier();

			if( arg1Type.hasTypeArrayOrStructure() )
			{
				if( compileAvmCode.second().is< InstanceOfData >() )
				{
					Symbol arg2( compileAvmCode.second() );

					if( arg1Type.isTEQ( arg2.referedTypeSpecifier() ) )
					{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "AvmcodeRelationalExpressionCompiler:>\n"
			<< "\t" << str_header( arg1 ) << std::endl
			<< "\t" << str_header( arg2 ) << std::endl;

	AVM_OS_TRACE << "Comparison of data structure << "
			<< compileAvmCode.str() << " >> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

						BFCode expandCode(
								aCode->isOpCode( AVM_OPCODE_NEQ ) ?
										OperatorManager::OPERATOR_OR :
										OperatorManager::OPERATOR_AND );

						compareStructure(aCTX->mCompileCtx, expandCode,
								aCode->getOperator(), arg1, arg2);

						if( expandCode->hasOneOperand() )
						{
							compileCode = expandCode->first();
						}
						else
						{
							compileCode = expandCode;
						}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "AvmcodeRelationalExpressionCompiler:result>\n"
			<< compileCode.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
					}
				}

				else if( compileAvmCode.second().is< ArrayBF >() )
				{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "AvmcodeRelationalExpressionCompiler:>\n"
			<< "\t" << str_header( arg1 ) << std::endl
			<< "\t" << compileAvmCode.second().str() << std::endl;

	AVM_OS_TRACE << "Comparison of data structre << "
			<< compileAvmCode.str() << " >> " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

					BFCode expandCode(
							aCode->isOpCode( AVM_OPCODE_NEQ ) ?
									OperatorManager::OPERATOR_OR :
									OperatorManager::OPERATOR_AND );

					compareStructure(aCTX->mCompileCtx, expandCode,
						aCode->getOperator(), arg1, compileAvmCode.second());

					if( expandCode->hasOneOperand() )
					{
						compileCode = expandCode->first();
					}
					else
					{
						compileCode = expandCode;
					}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << "AvmcodeRelationalExpressionCompiler:result>\n"
			<< compileCode.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
				}
			}
		}
		else if( compileAvmCode.second().is< InstanceOfData >() )
		{
			if( aCTX->isNeedTypeChecking() )
			{
				checkArgType(aCTX,
						compileAvmCode.second().to< InstanceOfData >()
						.getTypeSpecifier(), compileAvmCode.first());
			}
		}
	}

	return( compileCode );
}


BF AvmcodeRelationalExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	avm_arg_processor_t processor = AVM_ARG_ARITHMETIC_LOGIC_CPU;

	if( aCode->first().is< InstanceOfData >() &&
		aCode->first().to< InstanceOfData >().hasTypeArrayOrStructure() )
	{
		processor = AVM_ARG_ARRAY_RVALUE_CPU;
	}
	else if( aCode->second().is< InstanceOfData >() &&
			aCode->second().to< InstanceOfData >().hasTypeArrayOrStructure() )
	{
		processor = AVM_ARG_ARRAY_RVALUE_CPU;
	}
	else if( aCode->first().is< ArrayBF >() || aCode->second().is< ArrayBF >() )
	{
		processor = AVM_ARG_ARRAY_RVALUE_CPU;
	}

	return( optimizeBinaryRvalue( aCTX, aCode, TypeManager::UNIVERSAL,
			TypeManager::UNIVERSAL, processor, TypeManager::BOOLEAN) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE PREDICATE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryPredicateExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileUnaryRvalue(aCTX, aCode, TypeManager::BOOLEAN) );
}


BF AvmcodeUnaryPredicateExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeUnaryRvalue(aCTX, aCode, TypeManager::BOOLEAN,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::BOOLEAN) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE PREDICATE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryPredicateExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileBinaryRvalue(aCTX, aCode,
			TypeManager::BOOLEAN, TypeManager::BOOLEAN) );
}


BF AvmcodeBinaryPredicateExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeBinaryRvalue(aCTX, aCode,
			TypeManager::BOOLEAN, TypeManager::BOOLEAN,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::BOOLEAN) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE PREDICATE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAssociativePredicateExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileAssociativeRvalue(aCTX, aCode, TypeManager::BOOLEAN) );
}


BF AvmcodeAssociativePredicateExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeAssociativeRvalue(aCTX, aCode, TypeManager::BOOLEAN,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::BOOLEAN) );
}

////////////////////////////////////////////////////////////////////////////////
// AVMCODE PREDICATE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeQuantifiedPredicateExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode( aCode->getOperator() );

	BF aCompiledType;

	std::size_t offset = 0;
	for( const auto & itOperand : aCode.getOperands() )
	{
		if( itOperand.is< Variable >() )
		{
			const Variable & boundVariable = itOperand.to< Variable >();

			aCompiledType = compileArgRvalue(aCTX, boundVariable.getType());
			if( not aCompiledType.is< BaseTypeSpecifier >() )
			{
				getCompilerTable().incrErrorCount();
				aCTX->errorContext( AVM_OS_WARN )
						<< "AvmCode< quantified expression > :> "
							"Unexpected <<" << str_indent( aCompiledType )
						<< " >> as a type specifier of bound  variable :"
						<< IGNORE_FIRST_TAB << itOperand
						<< std::endl;

				return( aCode );
			}

			const BaseTypeSpecifier & aCompiledTypeSpecifier =
					aCompiledType.as< BaseTypeSpecifier >();

			Symbol boundSymbol( new InstanceOfData(
					IPointerVariableNature::POINTER_STANDARD_NATURE,
					aCTX->mCompileCtx, boundVariable,
					aCompiledTypeSpecifier, offset++ ) );
			newCode->append( boundSymbol );

			aCTX->mCompileCtx->appendVariableAlias( boundSymbol );
		}
		else if( itOperand.is< AvmCode >() )
		{
			BF arg = compileArgRvalue(
					aCTX->clone(TypeManager::BOOLEAN), itOperand);

			if( arg.invalid() )
			{
				getCompilerTable().incrErrorCount();
				aCTX->errorContext( AVM_OS_WARN )
						<< "AvmCode< quantified expression > compilation error << "
						<< itOperand.str() << " >>" << std::endl << std::endl;
			}

			newCode->append( arg );

			break;
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< quantified expression > compilation error << "
					<< itOperand.str() << " >>" << std::endl << std::endl;

			newCode->append( itOperand );
		}
	}

	return( newCode );
}


BF AvmcodeQuantifiedPredicateExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	std::size_t endVarOfsset = aCode->getOperands().size() - 1;
	for( std::size_t offset = 0 ; offset < endVarOfsset ; ++offset )
	{
		const InstanceOfData & boundVariable =
				aCode->operand(offset).as< InstanceOfData >();

		argsInstruction->set(offset,
				/*context  */ AVM_ARG_STANDARD_CTX,
				/*processor*/ AVM_ARG_NOP_CPU,
				/*operation*/ AVM_ARG_NOP_VALUE,
				/*operand  */ AVM_ARG_DATA_KIND,
				/*type     */ boundVariable.getTypeSpecifier() );
	}

	optimizeArgExpression(aCTX, aCode, endVarOfsset);
	argsInstruction->at(endVarOfsset).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(endVarOfsset), aCode->last());

	argsInstruction->setMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_ARITHMETIC_LOGIC_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ TypeManager::BOOLEAN.rawType() );

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE BITWISE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryBitwiseExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileUnaryRvalue(aCTX, aCode, TypeManager::INTEGER) );
}


BF AvmcodeUnaryBitwiseExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeUnaryRvalue(aCTX, aCode, TypeManager::INTEGER,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::INTEGER) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE BITWISE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryBitwiseExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileBinaryRvalue(aCTX, aCode,
			TypeManager::INTEGER, TypeManager::INTEGER) );
}


BF AvmcodeBinaryBitwiseExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeBinaryRvalue(aCTX, aCode,
			TypeManager::INTEGER, TypeManager::INTEGER,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::INTEGER) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE BITWISE EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAssociativeBitwiseExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileAssociativeRvalue(aCTX, aCode, TypeManager::INTEGER) );
}


BF AvmcodeAssociativeBitwiseExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeAssociativeRvalue(aCTX, aCode, TypeManager::INTEGER,
			AVM_ARG_ARITHMETIC_LOGIC_CPU, TypeManager::INTEGER) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE STRING UNARY EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeUnaryStringExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileUnaryRvalue(aCTX, aCode, TypeManager::STRING) );
}


BF AvmcodeUnaryStringExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeUnaryRvalue(aCTX, aCode, TypeManager::STRING,
			AVM_ARG_STRING_CPU, TypeManager::UNIVERSAL) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE STRING BINARY EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeBinaryStringExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileBinaryRvalue(aCTX, aCode,
			TypeManager::STRING, TypeManager::STRING) );
}


BF AvmcodeBinaryStringExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( optimizeBinaryRvalue(aCTX, aCode,
			TypeManager::STRING, TypeManager::STRING,
			AVM_ARG_STRING_CPU, TypeManager::UNIVERSAL) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ASSOCIATIVE BINARY EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeAssociativeStringExpressionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	const Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;
	AvmCode * pCode;

	aCTX = aCTX->clone(TypeManager::STRING);

	for( const auto & itOperand : aCode->getOperands() )
	{
		arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, itOperand);

		if( arg.valid() )
		{
			if( (not ExpressionTypeChecker::isTyped(TypeManager::STRING, arg))
					&& arg.isnot< BuiltinForm >() )
			{
				arg = ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_CTOR, TypeManager::STRING, arg);
			}
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > compilation error << "
					<< itOperand.str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			pCode = arg.to_ptr< AvmCode >();

			if( pCode->isOperator( mainOperator ) &&
				mainOperator->isAssociative() )
			{
				newCode->append( pCode->getOperands() );
			}
			else
			{
				newCode->append( arg );
			}
		}
		else
		{
			newCode->append( arg );
		}
	}

	return( newCode );
}


BF AvmcodeAssociativeStringExpressionCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	const Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;

	AvmInstruction * argsInstruction = newCode->newEmptyInstruction();

	Vector< AvmBytecode > vectorOfArgOpcode;

	for( const auto & itOperand : aCode->getOperands() )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, itOperand);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > optimization error << "
					<< itOperand.str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			const AvmCode & argCode = arg.to< AvmCode >();

			if( argCode.isOperator( mainOperator ) &&
				mainOperator->isAssociative() )
			{
				newCode->append( argCode.getOperands() );

				vectorOfArgOpcode.append(
						argCode.getInstruction()->getBytecode(), argCode.size());
			}
			else
			{
				newCode->append( arg );

				if( argCode.hasInstruction() )
				{
					vectorOfArgOpcode.append( argcodeOfExpression(aCTX, argCode) );
				}
				else
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected expression without argcode << "
							<< argCode.strDebug() << " >> !!!"
							<< SEND_EXIT;

					vectorOfArgOpcode.append( AvmBytecode(AVM_ARG_ARGUMENT_CTX,
							AVM_ARG_SEVAL_RVALUE, AVM_ARG_EXPRESSION_KIND) );
				}
				vectorOfArgOpcode.back().context = AVM_ARG_ARGUMENT_CTX;
			}
		}
		else
		{
			newCode->append( arg );

			AvmBytecode argOpcode;
			setArgcodeRValue(aCTX, argOpcode, arg, false);

			argOpcode.context = AVM_ARG_ARGUMENT_CTX;

			if( (not ExpressionTypeChecker::isTyped(TypeManager::STRING, arg))
					&& arg.is< BuiltinForm >() )
			{
				argOpcode.processor = AVM_ARG_STRING_CPU;
			}

			vectorOfArgOpcode.append( argOpcode );
		}
	}

	argsInstruction->setMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_STRING_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ TypeManager::STRING.rawType() );

	argsInstruction->computeBytecode( false , vectorOfArgOpcode );

	return( newCode );
}


} /* namespace sep */
