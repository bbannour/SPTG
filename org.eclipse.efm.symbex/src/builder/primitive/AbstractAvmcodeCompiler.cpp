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

#include "AbstractAvmcodeCompiler.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <computer/instruction/AvmInstruction.h>

#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Integer.h>
#include <fml/numeric/Rational.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/lib/AvmOperationFactory.h>
#include <fml/lib/ITypeSpecifier.h>

#include <fml/type/ContainerTypeSpecifier.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/Variable.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// SPECIFIC ARGUMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AbstractAvmcodeCompiler::compileArgLvalue(
		COMPILE_CONTEXT * aCTX, const BF & arg)
{
	BF compileArg;

	switch( arg.classKind() )
	{
		case FORM_XFSP_VARIABLE_KIND:
		{
			compileArg = AVMCODE_COMPILER.compileVariable(aCTX, arg);
			break;
		}

		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			if( arg.to_ptr< QualifiedIdentifier >()->isPositionalParameter() )
			{
				compileArg = AVMCODE_COMPILER.
						compileQualifiedPositionalIdentifier(aCTX, arg);
			}
			else if( arg.str().find(':') != std::string::npos )
			{
				compileArg = AVMCODE_COMPILER.
						compileFullyQualifiedNameID(aCTX, arg);
			}
			else
			{
				compileArg = AVMCODE_COMPILER.
						compileQualifiedIdentifier(aCTX, arg);
			}
			break;
		}
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			compileArg = AVMCODE_COMPILER.compileIdentifier(aCTX, arg);
			break;
		}

		case FORM_XFSP_BUFFER_KIND:
		case FORM_XFSP_CHANNEL_KIND:
		case FORM_XFSP_CONNECTOR_KIND:
		case FORM_XFSP_MACHINE_KIND:
		case FORM_XFSP_PORT_KIND:
		case FORM_XFSP_ROUTINE_KIND:
		case FORM_XFSP_SYSTEM_KIND:
		case FORM_XFSP_TRANSITION_KIND:
		case FORM_XFSP_DATATYPE_KIND:
		{
			compileArg = AVMCODE_COMPILER.compileElement(aCTX, arg);
			break;
		}

		case FORM_UFI_KIND:
		{
			compileArg = AVMCODE_COMPILER.compileUFI(
					aCTX, arg.to_ref< UniFormIdentifier>());
			break;
		}

		case FORM_AVMCODE_KIND:
		{
			compileArg = AVMCODE_COMPILER.compileExpression(aCTX, arg.bfCode());
			break;
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			compileArg = arg;
			break;
		}

		default:
		{
			compileArg = AVMCODE_COMPILER.decode_compileExpression(aCTX, arg);
			break;
		}
	}


	if( compileArg.valid() )
	{
		if( compileArg.is< InstanceOfData >() )
		{
			InstanceOfData * iodArg = compileArg.to_ptr< InstanceOfData >();

			if( iodArg->getModifier().hasFeatureMutable() )
			{
				if( iodArg->isAlias() )
				{
					if( not iodArg->getModifier().
							isVisibilityPublic( aCTX->getModifier() ) )
					{
						getCompilerTable().incrErrorCount();
						aCTX->errorContext( AVM_OS_WARN )
							<< "compileArgLvalue:> compilation error : "
							"Illegal access of non \"public\" LVALUE << "
							<< str_header( iodArg ) << " >> for << "
							<< arg.str() << " >>" << std::endl << std::endl;
					}
					if( not iodArg->getModifier().
							hasFeatureVolatile( aCTX->getModifier() ) )
					{
						if( iodArg->getAstElement()->isnot< ObjectElement >() )
						{
							getCompilerTable().incrErrorCount();
							aCTX->errorContext( AVM_OS_WARN )
								<< "compileArgLvalue:> compilation error : "
								"Illegal access of non \"volatile\" LVALUE << "
								<< str_header( iodArg ) << " >> for << "
								<< arg.str() << " >>" << std::endl << std::endl;
						}
					}
				}
				return( compileArg );
			}
			else
			{
				getCompilerTable().incrErrorCount();
				aCTX->errorContext( AVM_OS_WARN )
						<< "compileArgLvalue:> compilation error : "
						"Illegal access of a \"const\" LVALUE << "
						<< str_header( iodArg ) << " >> for << "
						<< arg.str() << " >>" << std::endl << std::endl;

				return( arg );
			}
		}
		else if( compileArg.is< AvmCode >() )
		{
			return( compileArg );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "compileArgLvalue:> compilation error : "
					"Unexpected << " << compileArg.str()
					<< " >> as LVALUE for << " << arg.str() << " >>"
					<< std::endl << std::endl;

			return( arg );
		}
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "compileArgLvalue:> compilation error << "
				<< arg.str() << " >>" << std::endl << std::endl;

		return( arg );
	}
}


BF AbstractAvmcodeCompiler::compileArgRvalue(
		COMPILE_CONTEXT * aCTX, const BF & arg, bool needTypeChecking)
{
	BF compileArg = AVMCODE_COMPILER.decode_compileExpression(aCTX, arg);

	if( compileArg.valid() )
	{
		if( compileArg.is< InstanceOfData >() )
		{
			InstanceOfData * iodArg = compileArg.to_ptr< InstanceOfData >();

			if( iodArg->getModifier().hasFeatureMutable() )
			{
				if( iodArg->isAlias() )
				{
					if( not iodArg->getModifier().
							isVisibilityPublic( aCTX->getModifier() ) )
					{
						getCompilerTable().incrErrorCount();
						aCTX->errorContext( AVM_OS_WARN )
								<< "compileArgLvalue:> compilation error : "
								"Illegal access of non \"public\" RVALUE << "
								<< str_header( iodArg ) << " >> for << "
								<< arg.str() << " >>" << std::endl << std::endl;
					}
				}
			}
		}
	}

	if( compileArg.valid() )
	{
		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			checkArgType(aCTX, aCTX->mType, compileArg);
		}

		return( compileArg );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "compileArgRvalue:> compilation error << "
				<< arg.str() << " >>" << std::endl << std::endl;

		return( arg );
	}
}



////////////////////////////////////////////////////////////////////////////////
// COMPILATION OF EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BFCode AbstractAvmcodeCompiler::compileExpressionCode(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;
	AvmCode * pCode;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();

	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, *itArg);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > compilation error << "
					<< (*itArg).str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			pCode = arg.to_ptr< AvmCode >();

			if( pCode->isOperator( mainOperator )
				&& mainOperator->isAssociative() )
			{
				newCode->append( pCode->getArgs() );
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


BFCode AbstractAvmcodeCompiler::optimizeExpressionCode(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode,
		avm_arg_operand_t anOperand)
{
	Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;
	AvmCode * pCode;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();

	AvmInstruction * argsInstruction = newCode->newEmptyInstruction();

	Vector< AvmBytecode > vectorOfArgOpcode;

	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, *itArg);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< expression > optimization error << "
					<< (*itArg).str() << " >>" << std::endl << std::endl;

			newCode->append( arg );
			continue;
		}

		if( arg.is< AvmCode >() )
		{
			pCode = arg.to_ptr< AvmCode >();

			if( pCode->isOperator( mainOperator )
				&& mainOperator->isAssociative() )
			{
				newCode->append( pCode->getArgs() );

				vectorOfArgOpcode.append(
						pCode->getInstruction()->getBytecode(),
						pCode->size());
			}
			else
			{
				newCode->append( arg );

				vectorOfArgOpcode.append( argcodeOfExpression(aCTX, pCode) );
			}
		}
		else
		{
			newCode->append( arg );

			AvmBytecode argOpcode;
			setArgcodeRValue(aCTX, argOpcode, arg, false);
			vectorOfArgOpcode.append( argOpcode );
		}
	}

	argsInstruction->setMainBytecode(
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ anOperand );

	argsInstruction->computeBytecode( false , vectorOfArgOpcode );

	return( newCode );
}


////////////////////////////////////////////////////////////////////////////////
// COMPILATION OF STATEMENT
////////////////////////////////////////////////////////////////////////////////

BFCode AbstractAvmcodeCompiler::compileStatementCode(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();

	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_compileStatement(aCTX, *itArg);

		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << "
					<< (*itArg).str() << " >>" << std::endl << std::endl;

			newCode->append( *itArg );
			continue;
		}

		switch( arg.classKind() )
		{
			case FORM_AVMCODE_KIND:
			{
				if( arg.to_ptr< AvmCode >()->isOpCode( mainOperator )
					&& mainOperator->isAssociative() )
				{
					newCode->append( arg.to_ptr< AvmCode >()->getArgs() );
				}
				else
				{
					newCode->append( arg );
				}

				break;
			}

			default:
			{
				newCode->append( arg );

				break;
			}
		}
	}

	return( newCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE COMPILATION STEP
////////////////////////////////////////////////////////////////////////////////

BFCode AbstractAvmcodeCompiler::compileAvmcode(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	Operator * mainOperator = aCode->getOperator();
	BFCode newCode( mainOperator );

	BF arg;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();

	for( ; itArg != itEndArg ; ++itArg )
	{
		switch( (*itArg).classKind() )
		{
			case FORM_AVMCODE_KIND:
			{
				arg = compileAvmcode(aCTX, (*itArg).bfCode());

				break;
			}

			default:
			{
				arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, *itArg);

				break;
			}
		}



		if( arg.invalid() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << "
					<< (*itArg).str() << " >>" << std::endl << std::endl;

			newCode->append( *itArg );
			continue;
		}

		switch( arg.classKind() )
		{
			case FORM_AVMCODE_KIND:
			{
				if( arg.to_ptr< AvmCode >()->isOperator( mainOperator )
					&& mainOperator->isAssociative() )
				{
					newCode->append( arg.to_ptr< AvmCode >()->getArgs() );
				}
				else
				{
					newCode->append( arg );
				}

				break;
			}

			default:
			{
				newCode->append( arg );

				break;
			}
		}
	}

	return( newCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVM OPCODE COMPILATION
////////////////////////////////////////////////////////////////////////////////

/**
 * operand
 */

bool AbstractAvmcodeCompiler::mustBeEvaluatedArgument(const BF & arg)
{
	switch( arg.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:

		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_STRING_KIND:
		{
			return( false );
		}

		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( true );
		}

		case FORM_AVMCODE_KIND:
		{
			return( true );
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			return( false );
		}

		case FORM_ARRAY_BF_KIND:
		{
			return( mustBeEvaluatedArgumentArray( arg.to_ptr< ArrayBF >() ) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			return( true );
		}

		case FORM_RUNTIME_ID_KIND:

		case FORM_INSTANCE_PORT_KIND:
		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		{
			return( false );
		}

		case FORM_OPERATOR_KIND:
		case FORM_AVMLAMBDA_KIND:
		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		case FORM_EXECUTABLE_MACHINE_KIND:
		case FORM_EXECUTABLE_SYSTEM_KIND:
		{
			return( false );
		}

		default:
		{
			return( true );
		}
	}
}


bool AbstractAvmcodeCompiler::mustBeEvaluatedArgumentArray(ArrayBF * arrayArg)
{
	for( avm_size_t idx = 0 ; idx < arrayArg->size() ; ++idx )
	{
		if( mustBeEvaluatedArgument(arrayArg->at(idx)) )
		{
			return( true );
		}
	}
	return( false );
}

avm_arg_operand_t AbstractAvmcodeCompiler::operandOf(const BF & arg)
{
	switch( arg.classKind() )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( AVM_ARG_BOOLEAN_KIND );
		}
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( AVM_ARG_INTEGER_KIND );
		}
		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( AVM_ARG_RATIONAL_KIND );
		}
		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( AVM_ARG_FLOAT_KIND );
		}

		case FORM_BUILTIN_CHARACTER_KIND:
		{
			return( AVM_ARG_CHARACTER_KIND );
		}
		case FORM_BUILTIN_STRING_KIND:
		{
			return( AVM_ARG_STRING_KIND );
		}

		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( AVM_ARG_BUILTIN_KIND );
		}

		case FORM_OPERATOR_KIND:
		{
			return( AVM_ARG_OPERATOR_KIND );
		}

		case FORM_AVMCODE_KIND:
		{
			return( AVM_ARG_EXPRESSION_KIND );
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			return( AVM_ARG_BUILTIN_ARRAY_KIND );
		}

		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * arrayArg = arg.to_ptr< ArrayBF >();
			for( avm_size_t idx = 0 ; idx < arrayArg->size() ; ++idx )
			{
				if( mustBeEvaluatedArgument(arrayArg->at(idx)) )
				{
					return( AVM_ARG_EXPRESSION_KIND );
				}
			}
			return( AVM_ARG_BUILTIN_ARRAY_KIND );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

			if( anInstance->isUfiMixedPointer() )
			{
				return( AVM_ARG_DATA_UFI_KIND );
			}
			else if( anInstance->getModifier().hasNatureReference() )
			{
				return( anInstance->isUfiOffsetPointer() ?
						AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND );
			}
			else if( anInstance->getModifier().hasNatureMacro() )
			{
				return( AVM_ARG_DATA_MACRO_KIND );
			}
			else if( anInstance->getModifier().hasFeatureMutable() )
			{
				return( AVM_ARG_DATA_KIND );
			}
			else if( anInstance->getModifier().hasModifierPublicFinalStatic() )
			{
				if( ExecutableLib::MACHINE_COMPONENT_SELF == anInstance )
				{
					return( AVM_ARG_COMPONENT_SELF_RID );
				}
				else if( ExecutableLib::MACHINE_COMPONENT_PARENT == anInstance )
				{
					return( AVM_ARG_COMPONENT_PARENT_RID );
				}
				else if( ExecutableLib::MACHINE_COMPONENT_COMMUNICATOR
						== anInstance )
				{
					return( AVM_ARG_COMPONENT_COMMUNICATOR_RID );
				}

				else if( ExecutableLib::MACHINE_ENVIRONMENT == anInstance )
				{
					return( AVM_ARG_ENVIRONMENT_RID );
				}

				else if( ExecutableLib::MACHINE_SYSTEM == anInstance )
				{
					return( AVM_ARG_SYSTEM_RID );
				}

				else if( ExecutableLib::MACHINE_SELF == anInstance )
				{
					return( AVM_ARG_SELF_RID );
				}
				else if( ExecutableLib::MACHINE_PARENT == anInstance )
				{
					return( AVM_ARG_PARENT_RID );
				}
				else if( ExecutableLib::MACHINE_COMMUNICATOR == anInstance )
				{
					return( AVM_ARG_COMMUNICATOR_RID );
				}
				else
				{
					return( AVM_ARG_DATA_CST_KIND );
				}
			}
			else if( anInstance->getModifier().hasFeatureFinal() )
			{
				return( AVM_ARG_DATA_CST_KIND );
			}
			else
			{
				return( AVM_ARG_DATA_KIND );
			}
		}

		case FORM_RUNTIME_ID_KIND:
		{
			return( AVM_ARG_MACHINE_RID );
		}

		case FORM_INSTANCE_PORT_KIND:
		{
			return( AVM_ARG_PORT_KIND );
		}
		case FORM_INSTANCE_BUFFER_KIND:
		{
			return( AVM_ARG_BUFFER_KIND );
		}
		case FORM_INSTANCE_CONNECTOR_KIND:
		{
			return( AVM_ARG_CONNECTOR_KIND );
		}

		case FORM_AVMLAMBDA_KIND:
		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		case FORM_EXECUTABLE_MACHINE_KIND:
		case FORM_EXECUTABLE_SYSTEM_KIND:
		{
			return( AVM_ARG_STATEMENT_KIND );
		}

		default:
		{
			return( AVM_ARG_UNDEFINED_OPERAND );
		}
	}
}


avm_arg_processor_t AbstractAvmcodeCompiler::processorOf(
		BaseTypeSpecifier * aType)
{
	switch( aType->getTypeSpecifierKind() )
	{
		case TYPE_BOOLEAN_SPECIFIER:
		case TYPE_INTEGER_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:
		{
			return( AVM_ARG_ARITHMETIC_LOGIC_CPU );
		}

		case TYPE_CHARACTER_SPECIFIER:
		{
			return( AVM_ARG_CHARACTER_CPU );
		}

		case TYPE_STRING_SPECIFIER:
		{
			return( AVM_ARG_STRING_CPU );
		}

		case TYPE_ARRAY_SPECIFIER:
		{
			return( AVM_ARG_ARRAY_RVALUE_CPU );
//			return( AVM_ARG_ARRAY_LVALUE_CPU );
		}

		case TYPE_VECTOR_SPECIFIER:
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		{
			return( AVM_ARG_VECTOR_CPU );
		}

		case TYPE_LIST_SPECIFIER:
		{
			return( AVM_ARG_LIST_CPU );
		}

		case TYPE_FIFO_SPECIFIER:
		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		case TYPE_RAM_SPECIFIER:
		{
			return( AVM_ARG_QUEUE_CPU );
		}

		case TYPE_SET_SPECIFIER:
		case TYPE_MULTISET_SPECIFIER:
		{
			return( AVM_ARG_COLLECTION_CPU );
		}

		default:
		{
			return( AVM_ARG_UNDEFINED_PROCESSOR );
		}
	}
}


avm_arg_operand_t AbstractAvmcodeCompiler::operandOf(BaseTypeSpecifier * aType)
{
	switch( aType->getTypeSpecifierKind() )
	{
		case TYPE_BOOLEAN_SPECIFIER:
		{
			return( AVM_ARG_BOOLEAN_KIND );
		}
		case TYPE_INTEGER_SPECIFIER:
		{
			return( AVM_ARG_INTEGER_KIND );
		}
		case TYPE_RATIONAL_SPECIFIER:
		{
			return( AVM_ARG_RATIONAL_KIND );
		}
		case TYPE_FLOAT_SPECIFIER:
		{
			return( AVM_ARG_FLOAT_KIND );
		}

		case TYPE_CHARACTER_SPECIFIER:
		{
			return( AVM_ARG_CHARACTER_KIND );
		}
		case TYPE_STRING_SPECIFIER:
		{
			return( AVM_ARG_STRING_KIND );
		}

		case TYPE_OPERATOR_SPECIFIER:
		{
			return( AVM_ARG_OPERATOR_KIND );
		}

		case TYPE_AVMCODE_SPECIFIER:
		{
			return( AVM_ARG_EXPRESSION_KIND );
		}

		case TYPE_ARRAY_SPECIFIER:
		{
			return( AVM_ARG_ARRAY_KIND );
		}

		default:
		{
			if( aType->hasTypeCollection() )
			{
				return( AVM_ARG_COLLECTION_KIND );
			}
			else
			{
				return( AVM_ARG_UNDEFINED_OPERAND );
			}
		}
	}
}



void AbstractAvmcodeCompiler::setArgcodeLValue(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg, bool needTypeChecking)
{
	argCode.processor = AVM_ARG_MEMORY_LVALUE_CPU;
	argCode.operation = AVM_ARG_SEVAL_LVALUE;

	if( arg.is< InstanceOfData >() )
	{
		InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			if( argCode.hasType() )
			{
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else if( aCTX->hasType() )
			{
				argCode.dtype = aCTX->mType;
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else
			{
				argCode.dtype = anInstance->getTypeSpecifier();
			}
		}
		else if( not argCode.hasType() )
		{
			argCode.dtype = anInstance->getTypeSpecifier();
		}

		if( anInstance->isUfiMixedPointer() )
		{
			argCode.operand   = AVM_ARG_DATA_UFI_KIND;
		}
		else if( anInstance->getModifier().hasNatureReference() )
		{
			argCode.operand   = (anInstance->isUfiOffsetPointer() ?
					AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND);
		}
		else if( anInstance->getModifier().hasNatureMacro() )
		{
			argCode.operand   = AVM_ARG_DATA_MACRO_KIND;
		}

		else if( anInstance->getModifier().hasFeatureMutable() )
		{
			argCode.processor = AVM_ARG_NOP_CPU;
			argCode.operation = AVM_ARG_NOP_LVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}
		else
		{
			getCompilerTable().incrWarningCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeLvalue :> Unexpected the InstanceOfData << "
					<< str_header( arg ) << " >> as << " << argCode.strType()
					<< " >> argument !!!" << std::endl;

			argCode.processor = AVM_ARG_NOP_CPU;
			argCode.operation = AVM_ARG_NOP_LVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}
	}

	else if( arg.is< AvmCode >() )
	{
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}

	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeLvalue :> Unexpected << "
				<< str_header( arg ) << " >> as lvalue argument typed by "
				<< argCode.strType() << " >> !!!" << std::endl;

		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}


void AbstractAvmcodeCompiler::setArgcodeLValueRef(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg, bool needTypeChecking)
{
	if( arg.is< InstanceOfData >()
		&& arg.to_ptr< InstanceOfData >()->getModifier().hasNatureReference() )
	{
		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			if( argCode.hasType() )
			{
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else if( aCTX->hasType() )
			{
				argCode.dtype = aCTX->mType;
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else
			{
				argCode.dtype = arg.to_ptr<
						InstanceOfData >()->getTypeSpecifier();
			}
		}
		else if( not argCode.hasType() )
		{
			argCode.dtype = arg.to_ptr<
					InstanceOfData >()->getTypeSpecifier();
		}

		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_LVALUE;
		argCode.operand   = AVM_ARG_DATA_REF_KIND;
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeLvalue :> Unexpected << "
				<< str_header( arg ) << " >> as << " << argCode.strType()
				<< " >> reference InstanceOfData argument !!!" << std::endl;

		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_LVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}


void AbstractAvmcodeCompiler::setArgcodeLValueMacro(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg, bool needTypeChecking)
{
	if( arg.is< InstanceOfData >()
		&& arg.to_ptr< InstanceOfData >()->getModifier().hasNatureMacro() )
	{
		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			if( argCode.hasType() )
			{
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else if( aCTX->hasType() )
			{
				argCode.dtype = aCTX->mType;
				checkArgType(aCTX, argCode.dtype, arg);
			}
			else
			{
				argCode.dtype = arg.to_ptr<
						InstanceOfData >()->getTypeSpecifier();
			}
		}
		else if( not argCode.hasType() )
		{
			argCode.dtype = arg.to_ptr<
					InstanceOfData >()->getTypeSpecifier();
		}

		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_LVALUE;
		argCode.operand   = AVM_ARG_DATA_MACRO_KIND;
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeLvalue :> Unexpected << "
				<< str_header( arg ) << " >> as << " << argCode.strType()
				<< " >> macro InstanceOfData argument !!!" << std::endl;

		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_LVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}


void AbstractAvmcodeCompiler::setArgcodeRValue(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, BF & arg, bool needTypeChecking)
{
	if( argCode.dtype->isTypedArray() )
	{
		setArgcodeRValueArray(aCTX, argCode, arg, needTypeChecking);

		return;
	}

	if( aCTX->isNeedTypeChecking(needTypeChecking) )
	{
		checkArgType(aCTX, argCode.dtype, arg);
	}

	if( arg.is< ArrayBF >() )
	{
		setArgcodeRValueArray(aCTX, argCode,
				arg.to_ptr< ArrayBF >(), needTypeChecking);
	}
	else if( arg.isBuiltinValue() )
	{
//		argCode.processor = AVM_ARG_ARITHMETIC_LOGIC_CPU;
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;

		if( arg.is< Boolean >() )
		{
			argCode.operand = AVM_ARG_BOOLEAN_KIND;
		}
		else if( arg.is< Integer >() )
		{
			argCode.operand = AVM_ARG_INTEGER_KIND;
		}
		else if( arg.is< Rational >() )
		{
			argCode.operand = AVM_ARG_RATIONAL_KIND;
		}
		else if( arg.is< Float >() )
		{
			argCode.operand = AVM_ARG_FLOAT_KIND;
		}
		else if( arg.is< Character >() )
		{
//			argCode.processor = AVM_ARG_CHARACTER_CPU;
			argCode.operand = AVM_ARG_CHARACTER_KIND;
		}
		else if( arg.is< String >() )
		{
//			argCode.processor = AVM_ARG_STRING_CPU;
			argCode.operand = AVM_ARG_STRING_KIND;
		}
		else
		{
			argCode.operand = AVM_ARG_BUILTIN_KIND;
		}
	}

	else if( arg.is< InstanceOfData >() )
	{
		InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

		argCode.processor = anInstance->isTypedMachine() ?
				AVM_ARG_MEMORY_MACHINE_CPU  :  AVM_ARG_MEMORY_RVALUE_CPU;

		argCode.operation = AVM_ARG_SEVAL_RVALUE;

		if( anInstance->isUfiMixedPointer() )
		{
			argCode.operand = AVM_ARG_DATA_UFI_KIND;
		}
		else if( anInstance->getModifier().hasNatureReference() )
		{
			argCode.operand = (anInstance->isUfiOffsetPointer() ?
					AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND);
		}
		else if( anInstance->getModifier().hasNatureMacro() )
		{
			argCode.operand = AVM_ARG_DATA_MACRO_KIND;
		}

		else if( anInstance->getModifier().hasFeatureMutable() )
		{
			argCode.operand = AVM_ARG_DATA_KIND;
		}

		else if( anInstance->getModifier().hasModifierPublicFinalStatic() )
		{
			if( anInstance->isTypedEnum() && anInstance->hasValue() )
			{
				arg = anInstance->getValue();
				setArgcodeRValue(aCTX, argCode, arg, false);
			}
			else
			{
				argCode.processor = AVM_ARG_MEMORY_MACHINE_CPU;

				if( ExecutableLib::MACHINE_COMPONENT_SELF == anInstance )
				{
					argCode.operand = AVM_ARG_COMPONENT_SELF_RID;
				}
				else if( ExecutableLib::MACHINE_COMPONENT_PARENT == anInstance )
				{
					argCode.operand = AVM_ARG_COMPONENT_PARENT_RID;
				}
				else if( ExecutableLib::MACHINE_COMPONENT_COMMUNICATOR == anInstance )
				{
					argCode.operand = AVM_ARG_COMPONENT_COMMUNICATOR_RID;
				}

				else if( ExecutableLib::MACHINE_ENVIRONMENT == anInstance )
				{
					argCode.operand = AVM_ARG_ENVIRONMENT_RID;
				}

				else if( ExecutableLib::MACHINE_SYSTEM == anInstance )
				{
					argCode.operand = AVM_ARG_SYSTEM_RID;
				}

				else if( ExecutableLib::MACHINE_SELF == anInstance )
				{
					argCode.operand = AVM_ARG_SELF_RID;
				}
				else if( ExecutableLib::MACHINE_PARENT == anInstance )
				{
					argCode.operand = AVM_ARG_PARENT_RID;
				}
				else if( ExecutableLib::MACHINE_COMMUNICATOR == anInstance )
				{
					argCode.operand = AVM_ARG_COMMUNICATOR_RID;
				}
				else
				{
					argCode.processor = AVM_ARG_NOP_CPU;
					argCode.operation = AVM_ARG_NOP_RVALUE;
					argCode.operand   = AVM_ARG_DATA_CST_KIND;
				}
			}
		}
		else if( anInstance->getModifier().hasFeatureFinal() )
		{
			argCode.processor = AVM_ARG_NOP_CPU;
			argCode.operation = AVM_ARG_NOP_RVALUE;
			argCode.operand   = AVM_ARG_DATA_CST_KIND;
		}

		else
		{
			getCompilerTable().incrWarningCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeRvalue :> Unexpected the InstanceOfData << "
					<< str_header( anInstance ) << " >> as << "
					<< argCode.strType() << " >> argument !!!" << std::endl;

			argCode.operation = AVM_ARG_NOP_RVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}

		if( argCode.dtype == TypeManager::UNIVERSAL )
		{
			argCode.dtype = anInstance->getTypeSpecifier();
		}

	}

	else if( arg.is< RuntimeID >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_MACHINE_RID;
	}

	else if( arg.is< InstanceOfMachine >() )
	{
		argCode.processor = AVM_ARG_MEMORY_MACHINE_CPU;

		if( (not argCode.hasType()) || argCode.dtype->isTypedMachine() )
		{
			argCode.operation = AVM_ARG_SEVAL_RVALUE;
			argCode.operand   = AVM_ARG_MACHINE_RID;
		}
		else
		{
			argCode.operation = AVM_ARG_NOP_RVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}
	}
	else if( arg.is< InstanceOfPort >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_PORT_KIND;
	}
	else if( arg.is< InstanceOfBuffer >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_BUFFER_KIND;
	}
	else if( arg.is< InstanceOfConnect >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_CONNECTOR_KIND;
	}

	else if( arg.is< BaseInstanceForm >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_DATA_KIND;
	}


	else if( arg.is< AvmCode >() )
	{
		if( not arg.to_ptr< AvmCode >()->hasInstruction() )
		{
			arg = AVMCODE_COMPILER.optimizeExpression(aCTX, arg.bfCode());
		}

		argCode = argcodeOfExpression(aCTX, arg.to_ptr< AvmCode >());
	}

	else if( arg.is< Operator >()
			&& ( (not argCode.hasType())
				|| argCode.dtype->isTypedOperator() ) )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_OPERATOR_KIND;
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeRvalue :> Unexpected << "
				<< str_header( arg ) << " >> as << " << argCode.strType()
				<< " >> argument !!!" << std::endl;

		argCode.processor = AVM_ARG_ARITHMETIC_LOGIC_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}


AvmBytecode AbstractAvmcodeCompiler::argcodeOfExpression(
		COMPILE_CONTEXT * aCTX, AvmCode * aCode)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aCode->hasInstruction() )
			<< "setArgcodeRvalue :> Unexpected << " << aCode->str()
			<< " >> without compileInstruction !!!"
			<< SEND_EXIT;

	AvmBytecode argCode = aCode->getInstruction()->getMainBytecode();

	if(StatementTypeChecker::isAssign(aCode) )
	{
		argCode.processor = AVM_ARG_MEMORY_RVALUE_CPU;
		if( argCode.isNopOperation() )
		{
			argCode.operation = AVM_ARG_SEVAL_RVALUE;
		}
	}
	else if(StatementTypeChecker::isCommunication(aCode) )
	{
		argCode.processor = AVM_ARG_STATEMENT_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_STATEMENT_KIND;
	}

	else if(ExpressionTypeChecker::isCtor(aCode) )
	{
		argCode.operand = AVM_ARG_EXPRESSION_KIND;
	}
	return( argCode );
}



void AbstractAvmcodeCompiler::setArgcodeRValueArray(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, BF & arg, bool needTypeChecking)
{
	ContainerTypeSpecifier * arrayT =
			argCode.dtype->as< ContainerTypeSpecifier >();

	if( arg.is< ArrayBF >() )
	{
		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			checkArgType(aCTX, argCode.dtype, arg);
		}

		ArrayBF * argArray = arg.to_ptr< ArrayBF >();


		if( argArray->size() < arrayT->size() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeRValueArray :> Too few element in array :>\n<< "
					<< arg.str() << " >>\nas type << " << arrayT->strT()
					<< " >> argument !!!" << std::endl;
		}
		else if( argArray->size() > arrayT->size() )
		{
			getCompilerTable().incrWarningCount();
			aCTX->warningContext( AVM_OS_WARN )
					<< "setArgcodeRValueArray :> Too much element in array\n<< "
					<< arg.str() << " >>\nas type << " << arrayT->strType()
					<< " >> argument !!!" << std::endl;

			ArrayBF * reducedArgArray = new ArrayBF(arrayT, arrayT->size());

			for( avm_size_t idx = 0 ; idx < arrayT->size() ; ++idx )
			{
				reducedArgArray->set(idx, argArray->at(idx));
			}

			arg.renew( reducedArgArray );

			setArgcodeRValueArray(aCTX, argCode,
					reducedArgArray, needTypeChecking);
		}
		else
		{
			setArgcodeRValueArray(aCTX, argCode,
					arg.to_ptr< ArrayBF >(), needTypeChecking);
		}
	}


	else if( arg.is< InstanceOfData >()
			&& ExpressionTypeChecker::weaklyTyped( arrayT,
					arg.to_ptr< InstanceOfData >()->getTypeSpecifier() ) )
	{
		argCode.processor = AVM_ARG_MEMORY_RVALUE_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_DATA_KIND;
	}

	else if( ExpressionTypeChecker::isTyped(arrayT, arg) )
	{
		argCode.processor = AVM_ARG_ARITHMETIC_LOGIC_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}

	else
	{
		while( arrayT->getContentsTypeSpecifier().isTypedArray() )
		{
			arrayT = arrayT->getContentsTypeSpecifier().rawContainer();
		}
		if( aCTX->isNeedTypeChecking(needTypeChecking) )
		{
			checkArgType(aCTX, arrayT->getContentsTypeSpecifier(), arg);
		}

		argCode.processor = AVM_ARG_ARRAY_RVALUE_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = operandOf(arg);
	}
}

void AbstractAvmcodeCompiler::setArgcodeRValueArray(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, ArrayBF * argArray, bool needTypeChecking)
{
	avm_size_t argArraySize = argArray->size();

	argCode.processor = AVM_ARG_ARRAY_RVALUE_CPU;
	argCode.operation = AVM_ARG_NOP_RVALUE;
	argCode.operand   = AVM_ARG_BUILTIN_ARRAY_KIND;

	for( avm_size_t idx = 0 ; idx < argArraySize ; ++idx )
	{
		if( mustBeEvaluatedArgument(argArray->at(idx)) )
		{
			argCode.operation = AVM_ARG_SEVAL_RVALUE;
			argCode.operand   = AVM_ARG_ARRAY_KIND;
			break;
		}
	}


	AvmInstruction * arrayInstruction = new AvmInstruction( argArraySize );

	argArray->setInstruction( arrayInstruction );

	// Global ArgCode
	arrayInstruction->setMainBytecode(argCode);

	if( argArray->getTypeSpecifier()->is< ClassTypeSpecifier >() )
	{
		ClassTypeSpecifier * structT =
				argArray->getTypeSpecifier()->to< ClassTypeSpecifier >();

		for( avm_size_t idx = 0 ; idx < argArraySize ; ++idx )
		{
			setArgcodeRValue(
					aCTX->clone(structT->getSymbolData(idx).getTypeSpecifier()),
					arrayInstruction->at(idx), argArray->at(idx), needTypeChecking);

			arrayInstruction->at(idx).offset = idx;
		}
	}
	else
	{
		if( argArray->getTypeSpecifier()->is< ContainerTypeSpecifier >() )
		{
			aCTX = aCTX->clone( argArray->getTypeSpecifier()->
					to< ContainerTypeSpecifier >()->getContentsTypeSpecifier() );
		}
		else
		{
			needTypeChecking = false;
		}

		for( avm_size_t idx = 0 ; idx < argArraySize ; ++idx )
		{
			setArgcodeRValue(aCTX, arrayInstruction->at(idx),
					argArray->at(idx), needTypeChecking);

			arrayInstruction->at(idx).offset = idx;
		}
	}
}


void AbstractAvmcodeCompiler::setArgcodeContainerWValue(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg)
{
	argCode.processor = AVM_ARG_MEMORY_WVALUE_CPU;

	if( arg.is< BuiltinContainer >() )
	{
		argCode.operation = AVM_ARG_SEVAL_WVALUE;
		argCode.operand   = AVM_ARG_BUILTIN_CONTAINER_KIND;
	}

	else if( arg.is< InstanceOfBuffer >() )
	{
		argCode.operation = AVM_ARG_SEVAL_WVALUE;
		argCode.operand   = AVM_ARG_BUFFER_KIND;
		argCode.dtype     = TypeManager::BUFFER;

	}

	else if( arg.is< InstanceOfData >() )
	{
		argCode.operation = AVM_ARG_SEVAL_WVALUE;

		InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

		if( anInstance->isUfiMixedPointer() )
		{
			argCode.operand = AVM_ARG_DATA_UFI_KIND;
		}
		else if( anInstance->getModifier().hasNatureReference() )
		{
			argCode.operand = (anInstance->isUfiOffsetPointer() ?
					AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND);
		}
		else if( anInstance->getModifier().hasNatureMacro() )
		{
			argCode.operand = AVM_ARG_DATA_MACRO_KIND;
		}

		else if( anInstance->getModifier().hasFeatureMutable() )
		{
			argCode.operand = AVM_ARG_DATA_KIND;
		}

		else
		{
			getCompilerTable().incrWarningCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeContainerWValue :> "
						"Unexpected the InstanceOfData << "
					<< str_header( anInstance ) << " >> as << "
					<< argCode.strType() << " >> argument !!!" << std::endl;

			argCode.operation = AVM_ARG_NOP_RVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}

		if( anInstance->isTypedBuffer() || anInstance->hasTypeCollection() )
		{
			argCode.dtype = anInstance->getTypeSpecifier();
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeContainerWValue :> Unexpected << "
					<< str_header( anInstance ) << " >> as << Collection< T >"
					<< " >> argument !!!" << std::endl;

			AVM_OS_WARN << "The type below, is there a type of "
					"collection ? If yes, you found a BUG ! "
					<< std::endl
					<< to_stream( anInstance->referedTypeSpecifier() );
		}
	}

	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeContainerWValue :> Unexpected << "
				<< str_header( arg ) << " >> as << container >> argument !!!"
				<< std::endl;

		argCode.operation = AVM_ARG_SEVAL_WVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}


void AbstractAvmcodeCompiler::setArgcodeContainerRValue(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg)
{
	if( arg.is< BuiltinContainer >() )
	{
		argCode.processor = AVM_ARG_COLLECTION_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_BUILTIN_CONTAINER_KIND;
	}

	else if( arg.is< InstanceOfBuffer >() )
	{
		argCode.processor = AVM_ARG_BUFFER_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_BUFFER_KIND;
		argCode.dtype     = TypeManager::BUFFER;

	}

	else if( arg.is< InstanceOfData >() )
	{
		argCode.processor = AVM_ARG_MEMORY_RVALUE_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;

		InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

		if( anInstance->isUfiMixedPointer() )
		{
			argCode.operand = AVM_ARG_DATA_UFI_KIND;
		}
		else if( anInstance->getModifier().hasNatureReference() )
		{
			argCode.operand = (anInstance->isUfiOffsetPointer() ?
					AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND);
		}
		else if( anInstance->getModifier().hasNatureMacro() )
		{
			argCode.operand = AVM_ARG_DATA_MACRO_KIND;
		}

		else if( anInstance->getModifier().hasFeatureMutable() )
		{
			argCode.operand = AVM_ARG_DATA_KIND;
		}

		else
		{
			getCompilerTable().incrWarningCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeContainerRValue :> "
						"Unexpected the InstanceOfData << "
					<< str_header( anInstance ) << " >> as << "
					<< argCode.strType() << " >> argument !!!" << std::endl;

			argCode.operation = AVM_ARG_NOP_RVALUE;
			argCode.operand   = AVM_ARG_DATA_KIND;
		}

		if( anInstance->isTypedBuffer()
			|| anInstance->isTypedString()
			|| anInstance->hasTypeCollection() )
		{
			argCode.dtype = anInstance->getTypeSpecifier();
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "setArgcodeContainerRValue :> Unexpected << "
					<< str_header( anInstance ) << " >> as << Collection< T >"
					<< " >> argument !!!" << std::endl;

			AVM_OS_WARN << "The type below, is there a type of "
					"collection ? if yes, you found a BUG ! "
					<< std::endl
					<< to_stream( anInstance->referedTypeSpecifier() );
		}
	}

	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeContainerRValue :> Unexpected << "
				<< arg.raw_pointer()->classKindInfo() << " : " << str_header( arg )
				<< " >> as << container >> argument !!!" << std::endl;

		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_EXPRESSION_KIND;
	}
}



void AbstractAvmcodeCompiler::setArgcodeStatement(COMPILE_CONTEXT * aCTX,
		AvmBytecode & argCode, const BF & arg, bool needTypeChecking)
{
	argCode.dtype  = TypeManager::AVMCODE;
	if( aCTX->isNeedTypeChecking(needTypeChecking) )
	{
		checkArgType(aCTX, argCode.dtype, arg);
	}

	argCode.operation = AVM_ARG_UNDEFINED_OPERATION;
	argCode.operand   = AVM_ARG_UNDEFINED_OPERAND;

	if( arg.is< InstanceOfData >() )
	{
		InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

		argCode.processor = AVM_ARG_MEMORY_RVALUE_CPU;
		argCode.operation = AVM_ARG_SEVAL_RVALUE;

		if( anInstance->isUfiMixedPointer() )
		{
			argCode.operand   = AVM_ARG_DATA_UFI_KIND;
		}
		else if( anInstance->getModifier().hasNatureReference() )
		{
			argCode.operand   = (anInstance->isUfiOffsetPointer() ?
					AVM_ARG_DATA_UFI_KIND : AVM_ARG_DATA_REF_KIND);
		}
		else if( anInstance->getModifier().hasNatureMacro() )
		{
			argCode.operand   = AVM_ARG_DATA_MACRO_KIND;
		}
		else if( anInstance->getModifier().hasFeatureMutable() )
		{
			argCode.operand   = AVM_ARG_DATA_KIND;
		}
	}
	else if( arg.is< AvmCode >() )
	{
		argCode.processor = AVM_ARG_NOP_CPU;
		argCode.operation = AVM_ARG_NOP_RVALUE;
		argCode.operand   = AVM_ARG_STATEMENT_KIND;
	}

	if( (argCode.operation == AVM_ARG_UNDEFINED_OPERATION)
		&& (argCode.operand == AVM_ARG_UNDEFINED_OPERAND) )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "setArgcodeStatement :> Unexpected << "
				<< str_header( arg ) << " >> as << "
				<< argCode.strType() << " >> argument !!!" << std::endl;

		argCode.operation = AVM_ARG_SEVAL_RVALUE;
		argCode.operand   = AVM_ARG_STATEMENT_KIND;
	}
}



ExecutableForm * AbstractAvmcodeCompiler::getExecutableMachine(
		COMPILE_CONTEXT * aCTX, const BF & arg)
{
	switch( arg.classKind() )
	{
		case FORM_RUNTIME_ID_KIND:
		{
			return( arg.bfRID().getExecutable() );
		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
			return( arg.to_ptr< InstanceOfMachine >()->getExecutable() );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			InstanceOfData * anInstance = arg.to_ptr< InstanceOfData >();

			if( anInstance->isTypedMachine()
				&& anInstance->getModifier().hasModifierPublicFinalStatic() )
			{
				ExecutableForm * anExecutable = aCTX->mCompileCtx->getExecutable();

				if( ExecutableLib::MACHINE_COMPONENT_SELF == anInstance )
				{
					while( anExecutable != NULL )
					{
						if( anExecutable->isMainComponent() )
						{
							return( anExecutable );
						}
						anExecutable = anExecutable->getExecutableContainer();
					}
					return( anExecutable );
				}
				else if( ExecutableLib::MACHINE_COMPONENT_PARENT == anInstance )
				{
					for( bool isParent = false ; anExecutable != NULL ;  )
					{
						if( anExecutable->isMainComponent() )
						{
							if( isParent )
							{
								return( anExecutable );
							}
							isParent = true;
						}
						anExecutable = anExecutable->getExecutableContainer();
					}
					return( anExecutable );
				}
				else if( ExecutableLib::MACHINE_COMPONENT_COMMUNICATOR
						== anInstance )
				{
					while( anExecutable != NULL )
					{
						if( anExecutable->isMainComponent()
							&& anExecutable->hasPort() )
						{
							return( anExecutable );
						}
						anExecutable = anExecutable->getExecutableContainer();
					}
					return( anExecutable );
				}

				else if( ExecutableLib::MACHINE_SYSTEM == anInstance )
				{
					while( anExecutable->hasContainer()  )
					{
						anExecutable = anExecutable->getExecutableContainer();
					}
					return( anExecutable );
				}

				if( ExecutableLib::MACHINE_SELF == anInstance )
				{
					return( anExecutable );
				}
				else if( ExecutableLib::MACHINE_PARENT == anInstance )
				{
					return( anExecutable->getExecutableContainer() );
				}
				else if( ExecutableLib::MACHINE_COMMUNICATOR == anInstance )
				{
					while( anExecutable != NULL )
					{
						if( anExecutable->hasPort() )
						{
							return( anExecutable );
						}
						anExecutable = anExecutable->getExecutableContainer();
					}
					return( anExecutable );
				}
			}

			return( NULL );
		}

		case FORM_UFI_KIND:
		case FORM_AVMCODE_KIND:
		default:
		{
			return( NULL );
		}
	}

	return( NULL );
}



void AbstractAvmcodeCompiler::checkArgType(COMPILE_CONTEXT * aCTX,
		BaseTypeSpecifier * aType, const BF & arg)
{
	if( (aType == NULL) || aType->isTypedUniversal() )
	{
		return;
	}
	else if( not ExpressionTypeChecker::isTyped(aType, arg) )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "checkArgType :> Unexpected << ";

AVM_IF_DEBUG_FLAG( COMPILING )
	AVM_OS_WARN << std::endl << arg;
AVM_ELSE
	AVM_OS_WARN << str_header( arg );
AVM_ENDIF_DEBUG_FLAG( COMPILING )

		AVM_OS_WARN << " >> as << " << aType->strT()
				<< " >> argument !!!" << std::endl;

		if( aType->isTypedAlias() )
		{
			AVM_OS_WARN << "Info: << " << aType->strT()
					<< " >> is an alias or a typedef of :> "
					<< aType->referedTypeSpecifier()->strT() << std::endl;
		}
	}
}


}
