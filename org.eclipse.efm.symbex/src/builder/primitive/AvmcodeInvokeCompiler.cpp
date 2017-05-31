/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeInvokeCompiler.h"

#include <parser/model/ParserUtil.h>

#include <fml/executable/AvmLambda.h>
#include <fml/executable/AvmProgram.h>
#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableForm.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/lib/AvmOperationFactory.h>

#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/Machine.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE NEW INSTANCE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInvokeNewCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileExpressionCode(aCTX, aCode) );

//[REGRESSION]!TODO
//	return( compileStatement(aCTX, aCode) );
}


BF AvmcodeInvokeNewCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
//[REGRESSION]!TODO
//	BFCode newCode = optimizeStatement(aCTX, aCode);
//
//	newCode->getInstruction()->setMainBytecode(
//			/*context  */ AVM_ARG_RETURN_CTX,
//			/*processor*/ AVM_ARG_MEMORY_MACHINE_CPU,
//			/*operation*/ AVM_ARG_SEVAL_RVALUE,
//			/*operand  */ AVM_ARG_EXPRESSION_KIND,
//			/*dtype    */ newCode->getInstruction()->at(0).dtype);
//
//	return( aCode );


	BFCode optimizedCode( aCode->getOperator() );

	AvmCode::const_iterator it = aCode->begin();
	AvmCode::const_iterator endIt = aCode->end();

	AvmInstruction * argsInstruction =
			optimizedCode->newInstruction( aCode->size() );

	InstanceOfMachine * dynamicInstance = NULL;

	BF arg = (*it);

	optimizedCode->append( arg );

	if( arg.is< InstanceOfMachine >() )
	{
		dynamicInstance = arg.to_ptr< InstanceOfMachine >();

		argsInstruction->at(0).set(
				/*context  */ AVM_ARG_ARGUMENT_CTX,
				/*processor*/ AVM_ARG_NOP_CPU,
				/*operation*/ AVM_ARG_NOP_RVALUE,
				/*operand  */ AVM_ARG_MACHINE_RID,
				/*type     */ dynamicInstance->getTypeSpecifier()
				);
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "optimizeStatement :> Unexpected << " << str_header( arg )
				<< " >>  as invoke#new first argument in << "
				<< aCode->str() << " >> !!!" << std::endl;

		return( aCode );
	}

	avm_size_t paramCount = dynamicInstance->getParamCount();
	for( avm_size_t offset = 1 ;
			(++it != endIt) && (offset <= paramCount) ; ++offset )
	{
		arg = AVMCODE_COMPILER.decode_optimizeExpression(aCTX, (*it));
		optimizedCode->append( arg );

		argsInstruction->at(offset).dtype =
				dynamicInstance->getParamType( offset-1 );
		setArgcodeRValue(aCTX, argsInstruction->at(offset), arg);
	}

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_ARGUMENT_CTX,
			/*processor*/ AVM_ARG_MEMORY_MACHINE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND);

	return( optimizedCode );

}


BFCode AvmcodeInvokeNewCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() != 1 )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unexpected INVOKE#NEW without only one runnable "
					"#dynamic instance machine !!!"
				<< std::endl << aCode.toString()
				<< SEND_EXIT;
	}

	BFCode newCode = AbstractAvmcodeCompiler::compileExpressionCode(aCTX, aCode);

	const BF & arg = newCode->first();
	if( arg.is< InstanceOfMachine >() )
	{
		if( arg.to_ptr< InstanceOfMachine >()->
				getSpecifier().isDesignInstanceDynamic() )
		{
//!![MIGRATION]: see Compiler::precompileExecutableInstanceDynamique(...)
//			modelMachine->incrPossibleDynamicInstanciationCount(1);
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "Unexpected INVOKE#NEW with one runnable "
						"#dynamic instance machine !!!"
					<< std::endl << newCode.toString()
					<< SEND_EXIT;
		}
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unexpected INVOKE#NEW without one "
						"runnable #dynamic #instance machine !!!"
				<< std::endl << newCode.toString()
				<< SEND_EXIT;
	}

	return( newCode );
}


BFCode AvmcodeInvokeNewCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	const BF & arg = aCode->first();
	if( arg.is< InstanceOfMachine >()
		&& arg.to_ptr< InstanceOfMachine >()->
				getSpecifier().isDesignInstanceDynamic() )
	{
		AvmInstruction * argsInstruction = aCode->newInstruction( aCode->size() );

		InstanceOfMachine * dynamicInstance = arg.to_ptr< InstanceOfMachine >();

		argsInstruction->at(0).set(
				/*context  */ AVM_ARG_ARGUMENT_CTX,
				/*processor*/ AVM_ARG_NOP_CPU,
				/*operation*/ AVM_ARG_NOP_RVALUE,
				/*operand  */ AVM_ARG_MACHINE_RID,
				/*type     */ dynamicInstance->getTypeSpecifier()
				);

		argsInstruction->setMainBytecode(
				/*context  */ AVM_ARG_STANDARD_CTX,
				/*processor*/ AVM_ARG_NOPS_CPU,
				/*operation*/ AVM_ARG_NOPS_RVALUE,
				/*operand  */ AVM_ARG_STATEMENT_KIND,
				/*dtype    */ argsInstruction->at(0).dtype);
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "optimizeStatement: Unexpected statement << invoke#new >> "
						"argument !!!\n\t" << str_header( arg )
				<< std::endl << to_stream( aCode ) << std::endl;

		return( aCode );
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE ROUTINE COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInvokeRoutineCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BFCode AvmcodeInvokeRoutineCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
//	if( aCode->singleton &&  aCode->first().is< Routine >() )
//	{
//		return( ParserUtil::invokeRoutineExpression(
//				aCode->first().to_ptr< Routine >() ) );
//	}
//	else
	if( aCode->size() < 2 )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Expected invokable expression like "
					"(: form invokable ...) << " << aCode.str() << " >>"
				<< std::endl << std::endl;

		return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
	}

	BFCode newCode;

	BF arg = AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->first());
	if( arg.invalid() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "AvmCode< statement > compilation error << (: "
				<< aCode->first().str() << " ...) >>"
				<< std::endl << std::endl;

		return( aCode );
	}


	if( aCode->second().is< Operator >() )
	{
		newCode = StatementConstructor::newCode(
				aCode->second().to_ptr< Operator >(), arg);
	}
	else if( aCode->second().isIdentifier() )
	{
		Operator * op = AvmOperationFactory::get(arg,
				aCode->second().toIdentifier());
		if( op != NULL )
		{
			newCode = StatementConstructor::newCode(op, arg);
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << (: "
					<< arg.str() << " " << aCode->second().str() <<  " ...) >>"
					<< std::endl << std::endl;

			return( aCode );
		}
	}

	AvmCode::iterator itArg = aCode->begin() + 2;
	AvmCode::iterator itEndArg = aCode->end();
	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_compileStatement(aCTX, *itArg);

		if( arg.valid() )
		{
			newCode->append( arg );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << "
					<< (*itArg).str() << " >>"
					<< std::endl << std::endl;

			newCode->append( *itArg );
			continue;
		}
	}

	return( newCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE TRANSITION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeInvokeTransitionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() != 1 )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unexpected more than one argument for invoke#transition << "
				<< aCode.str() << " >>"
				<< std::endl << std::endl;

		return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
	}

	BF arg = AVMCODE_COMPILER.decode_compileStatement(aCTX, aCode->first());
	if( arg.invalid() || arg.isnot< AvmTransition >() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "AvmCode< statement > compilation error << (: "
				<< aCode->first().str() << " ...) >>"
				<< std::endl << std::endl;

		return( aCode );
	}

	return( StatementConstructor::newCode(aCode->getOperator(), arg) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE METHOD COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInvokeMethodCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() < 2 )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Expected invokable expression like (: form invokable ...) << "
				<< aCode.str() << " >>"
				<< std::endl << std::endl;

		return( AbstractAvmcodeCompiler::compileExpression(aCTX, aCode) );
	}

	BFCode newCode;

	BF arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, aCode->first());
	if( arg.invalid() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "AvmCode< statement > compilation error << (: "
				<< aCode->first().str() << " ...) >>"
				<< std::endl << std::endl;

		return( aCode );
	}


	if( aCode->second().is< Operator >() )
	{
		newCode = StatementConstructor::newCode(
				aCode->second().to_ptr< Operator >(), arg);
	}
	else if( aCode->second().isIdentifier() )
	{
		Operator * op = AvmOperationFactory::get(arg,
				aCode->second().toIdentifier());
		if( op != NULL )
		{
			newCode = StatementConstructor::newCode(op, arg);
		}
		else
		{
//			TypeManager::get

			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << (: "
					<< arg.str() << " " << aCode->second().str() << " ...) >>"
					<< std::endl << std::endl;

			return( aCode );
		}
	}

	AvmCode::iterator itArg = aCode->begin() + 2;
	AvmCode::iterator itEndArg = aCode->end();
	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, *itArg);

		if( arg.valid() )
		{
			newCode->append( arg );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << "
					<< (*itArg).str() << " >>"
					<< std::endl << std::endl;

			newCode->append( *itArg );
			continue;
		}
	}

	return( AVMCODE_COMPILER.compileExpression(aCTX, newCode) );
}

BFCode AvmcodeInvokeMethodCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() < 2 )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Expected invokable expression like "
					"(: form invokable ...) << " << aCode.str() << " >>"
				<< std::endl << std::endl;

		return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
	}

	BFCode newCode;

	BF arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, aCode->first());
	if( arg.invalid() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "AvmCode< statement > compilation error << (: "
				<< aCode->first().str() << " ...) >>"
				<< std::endl << std::endl;

		return( aCode );
	}


	if( aCode->second().is< Operator >() )
	{
		newCode = StatementConstructor::newCode(
				aCode->second().to_ptr< Operator >(), arg);
	}
	else if( aCode->second().isIdentifier() )
	{
		Operator * op = AvmOperationFactory::get(arg,
				aCode->second().toIdentifier());
		if( op != NULL )
		{
			newCode = StatementConstructor::newCode(op, arg);
		}
		else
		{
//			TypeManager::get

			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << (: "
					<< arg.str() << " " << aCode->second().str() << " ...) >>"
					<< std::endl << std::endl;

			return( aCode );
		}
	}

	AvmCode::iterator itArg = aCode->begin() + 2;
	AvmCode::iterator itEndArg = aCode->end();
	for( ; itArg != itEndArg ; ++itArg )
	{
		arg = AVMCODE_COMPILER.decode_compileExpression(aCTX, *itArg);

		if( arg.valid() )
		{
			newCode->append( arg );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "AvmCode< statement > compilation error << "
					<< (*itArg).str() << " >>"
					<< std::endl << std::endl;

			newCode->append( *itArg );
			continue;
		}
	}

	return( AVMCODE_COMPILER.compileStatement(aCTX, newCode) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE PROGRAM COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInvokeProgramCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BFCode AvmcodeInvokeProgramCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE INVOKE FUNCTION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeInvokeFunctionCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( compileStatement(aCTX, aCode) );
}

BFCode AvmcodeInvokeFunctionCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );

}



}
