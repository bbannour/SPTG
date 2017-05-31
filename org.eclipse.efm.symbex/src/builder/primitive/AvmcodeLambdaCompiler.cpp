/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeLambdaCompiler.h"

#include <fml/executable/AvmLambda.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE LAMBDA APPLY COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeLambdaApplyCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( not aCode->populated() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected APP EXPRESSION with less than 2 arguments "
					"for compileAvmCodeApp\n" << aCode->toString()
				<< SEND_EXIT;
	}

	BF aLambdaExpression = compileArgRvalue(aCTX, aCode->first());

	if( aLambdaExpression.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Error:> compiling LAMBDA EXPRESSION << "
				<< aCode->first().str() << " >> for compileAvmCodeApp\n"
				<< aCode->toString()
				<< SEND_EXIT;
	}

	BFCode newCode( aCode->getOperator() , aLambdaExpression);

//	BF appVar;

	BF lambdaValue;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();
	for( ++itArg ; itArg != itEndArg ; ++itArg )
	{
		lambdaValue = compileArgRvalue(aCTX, (*itArg));
		if( lambdaValue.valid() )
		{
			newCode->append( lambdaValue );
		}
		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Error:> compiling LAMBDA VALUE << "
					<< (*itArg).str() << " >> for compileAvmCodeApp\n"
					<< aCode->toString()
					<< SEND_EXIT;
		}

//		if( (*itArg).isnot< AvmCode >() )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected AVMCODE as variable-value association << "
//					<< (*itArg).str() << " >> for compileAvmCodeApp\n"
//					<< aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		const BFCode & appAssign = (*itArg).bfAvmCode();
//
//		if( appAssign->isnotOperator( OperatorManager::OPERATOR_ASSIGN ) )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected OPERATOR KIND in variable-value "
//						"association << " << appAssign->str()
//					<< " >> for compileAvmCodeApp\n" << aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		appVar = appAssign->first();
//
//		if( not appVar.isUFID() )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected VARIABLE KIND in variable-value "
//						"association << " << appAssign->str()
//					<< " >> for compileAvmCodeApp\n" << aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		const BF & lambdaVar = appAvmLambda->getSymbol( appVar.str() );
//		lambdaValue = compileArgRvalue(appAvmLambda, appAssign->second());
//
//		if( lambdaVar.valid && lambdaValue.valid() )
//		{
//			lambdaVar->setValue( lambdaValue );
//		}
	}

	return( newCode );
}

BFCode AvmcodeLambdaApplyCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( not aCode->populated() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected APP EXPRESSION with less than 2 arguments "
					"for compileAvmCodeApp\n" << aCode->toString()
				<< SEND_EXIT;

		return( BFCode::REF_NULL );
	}

	BF aLambdaExpression = AVMCODE_COMPILER.decode_compileStatement(aCTX,
			aCode->first());

	if( aLambdaExpression.invalid() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Error:> compiling LAMBDA EXPRESSION << "
				<< aCode->first().str() << " >> for compileAvmCodeApp\n"
				<< aCode->toString()
				<< SEND_EXIT;
	}

	BFCode newCode( aCode->getOperator() , aLambdaExpression);

//	BF appVar;

//	InstanceOfData * lambdaVar = NULL;
	BF lambdaValue;

	AvmCode::iterator itArg = aCode->begin();
	AvmCode::iterator itEndArg = aCode->end();
	for( ++itArg ; itArg != itEndArg ; ++itArg )
	{
		lambdaValue = AVMCODE_COMPILER.decode_compileStatement(aCTX, (*itArg));
		if( lambdaValue.valid() )
		{
			newCode->append( lambdaValue );
		}
		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Error:> compiling LAMBDA VALUE << "
					<< (*itArg).str() << " >> for compileAvmCodeApp\n"
					<< aCode->toString()
					<< SEND_EXIT;
		}

//		if( (*itArg).isnot< AvmCode >() )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected AVMCODE as variable-value "
//					"association << " << (*itArg).str()
//					<< " >> for compileAvmCodeApp\n" << aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		const BFCode & appAssign = (*itArg).bfCode();
//
//		if( appAssign->isnotOperator( OperatorManager::OPERATOR_ASSIGN ) )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected OPERATOR KIND in variable-value "
//						"association << " << appAssign->str()
//					<< " >> for compileAvmCodeApp\n" << aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		appVar = appAssign->first();
//
//		if( not appVar.isUFID() )
//		{
//			AVM_OS_EXIT( FAILED )
//					<< "Unexpected VARIABLE KIND in variable-value "
//						"association << " << appAssign->str()
//					<< " >> for compileAvmCodeApp\n" << aCode->toString()
//					<< SEND_EXIT;
//		}
//
//		const BF & lambdaVar = appAvmLambda->getSymbol( appVar.str() );
//		lambdaValue = AVMCODE_COMPILER.decode_compileStatement(appAvmLambda,
//				appAssign->second());
//
//		if( lambdaVar.valid() && lambdaValue.valid() )
//		{
//			lambdaVar.to_ptr< InstanceOfData >()->setValue( lambdaValue );
//		}
	}

	return( newCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE LAMBDA LET COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeLambdaLetCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( not aCode->populated() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected LAMBDA EXPRESSION without argument for "
					"compileAvmCodeLet\n" << aCode->toString()
				<< SEND_EXIT;

		return( BF::REF_NULL );
	}

	avm_size_t varCount = aCode->size() - 1;

	AvmLambda * letAvmLambda = new AvmLambda(
			aCTX->mCompileCtx, varCount, AVM_LAMBDA_LET_NATURE);

	BF bfLetLambda( letAvmLambda );

	BF letVar;
	BF letValue;

	BFCode letAssign;
	BF letVarForm;
	Variable * letVariable;
	InstanceOfData * lambdaInstance;

	AvmCode::iterator itArg = aCode->begin();
	for( avm_size_t offset = 0 ; offset < varCount ; ++itArg , ++offset )
	{
		if( (*itArg).is< AvmCode >() )
		{
			letAssign = (*itArg).bfCode();

			if( letAssign->getOperator() == OperatorManager::OPERATOR_ASSIGN )
			{
				letVar = letAssign->first();

				letValue = letAssign->second();
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "Unexpected OPERATOR KIND in variable-value "
							"association << " << letAssign->str()
						<< " >> for compileAvmCodeLet\n" << aCode->toString()
						<< SEND_EXIT;
			}
		}
		else
		{
			letVar = (*itArg);

			letValue.destroy();
			letAssign.destroy();
		}


		if( letVar.isIdentifier() || letVar.isUfi() ||
				letVar.is< UniFormIdentifier >() )
		{
			letVarForm = BF( letVariable = new Variable(
					const_cast< ObjectElement * >(
							aCTX->mCompileCtx->getAstElement() ),
					TypeManager::UNIVERSAL, letVar.str(), letVar.str()) );

			lambdaInstance = new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					letAvmLambda, letVariable, TypeManager::UNIVERSAL,
					offset, Modifier::PROPERTY_PARAMETER_MODIFIER );

			letAvmLambda->setData(offset, lambdaInstance);

			if( letValue.valid() )
			{
				letAssign->set(0, letVarForm);

				lambdaInstance->setValue( compileArgRvalue(aCTX, letValue) );
			}
			else
			{
				aCode->set(offset, letVarForm);
			}
		}

		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unexpected LAMBDA VARIABLE << " << letVar.str()
					<< " >> for compileAvmCodelet\n" << aCode->toString()
					<< SEND_EXIT;
		}
	}

	letAvmLambda->setExpression( compileArgRvalue(
			aCTX->newCTX(letAvmLambda, aCTX->mRuntimeCtx), aCode->last()) );

	return( bfLetLambda );
//	return( ExpressionConstructor::newCode(
//			OperatorManager::OPERATOR_INVOKE_LAMBDA_LET, letAvmLambda) );
}

BFCode AvmcodeLambdaLetCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( not aCode->populated() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected LAMBDA EXPRESSION without argument "
					"for compileAvmCodeLet\n" << aCode->toString()
				<< SEND_EXIT;

		return( BFCode::REF_NULL );
	}

	avm_size_t varCount = aCode->size() - 1;

	AvmLambda * letAvmLambda = new AvmLambda(
			aCTX->mCompileCtx, varCount, AVM_LAMBDA_LET_NATURE);

	BF bfLetLambda( letAvmLambda );

	BF letVar;
	BF letValue;

	BFCode letAssign;
	BF letVarForm;
	Variable * letVariable;
	InstanceOfData * lambdaInstance;

	AvmCode::iterator itArg = aCode->begin();
	for( avm_size_t offset = 0 ; offset < varCount ; ++itArg , ++offset )
	{
		if( (*itArg).is< AvmCode >() )
		{
			letAssign = (*itArg).bfCode();

			if( letAssign->getOperator() == OperatorManager::OPERATOR_ASSIGN )
			{
				letVar = letAssign->first();

				letValue = letAssign->second();
			}
			else
			{
				AVM_OS_EXIT( FAILED )
						<< "Unexpected OPERATOR KIND in variable-value "
							"association << " << letAssign->str()
						<< " >> for compileAvmCodeLet\n" << aCode->toString()
						<< SEND_EXIT;
			}
		}
		else
		{
			letVar = (*itArg);

			letValue.destroy();
			letAssign.destroy();
		}


		if( letVar.isIdentifier() || letVar.isUfi() ||
				letVar.is< UniFormIdentifier >() )
		{
			letVarForm = BF( letVariable = new Variable(
					const_cast< ObjectElement * >(
							aCTX->mCompileCtx->getAstElement() ),
					TypeManager::UNIVERSAL, letVar.str(), letVar.str()) );

			lambdaInstance = new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					letAvmLambda, letVariable, TypeManager::UNIVERSAL,
					offset, Modifier::PROPERTY_PARAMETER_MODIFIER );
			letAvmLambda->setData(offset, lambdaInstance);

			if( letValue.valid() )
			{
				letAssign->set(0, letVarForm);

				lambdaInstance->setValue(
					AVMCODE_COMPILER.decode_compileStatement(aCTX, letValue) );
			}
			else
			{
				aCode->set(offset, letVarForm);
			}
		}

		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unexpected LAMBDA VARIABLE << " << letVar.str()
					<< " >> for compileAvmCodelet\n" << aCode->toString()
					<< SEND_EXIT;
		}
	}

	letAvmLambda->setExpression( AVMCODE_COMPILER.decode_compileStatement(
			aCTX->newCTX(letAvmLambda, aCTX->mRuntimeCtx), aCode->last()) );

	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_INVOKE_LAMBDA_LET, bfLetLambda) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE LAMBDA EXPRESSION COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeLambdaExprCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected LAMBDA EXPRESSION without argument "
					"for compileAvmCodeLambda\n" << aCode->toString()
				<< SEND_EXIT;

		return( BF::REF_NULL );
	}

	avm_size_t varCount = aCode->size() - 1;

	AvmLambda * funAvmLambda = new AvmLambda(
			aCTX->mCompileCtx, varCount, AVM_LAMBDA_FUN_NATURE);

	BF bfFunLambda( funAvmLambda );

	BF lambdaVar;
	BF lambdaVarForm;
	Variable * lambdaVariable;
	InstanceOfData * lambdaInstance;

	AvmCode::iterator itArg = aCode->begin();
	for( avm_size_t offset = 0 ; offset < varCount ; ++itArg , ++offset )
	{
		lambdaVar = (*itArg);

		if( lambdaVar.isIdentifier() || lambdaVar.isUfi() ||
				lambdaVar.is< UniFormIdentifier >() )
		{
			lambdaVarForm = BF( lambdaVariable = new Variable(
					const_cast< ObjectElement * >(
							aCTX->mCompileCtx->getAstElement() ),
					TypeManager::UNIVERSAL, lambdaVar.str(), lambdaVar.str()) );
			aCode->set(offset, lambdaVarForm);

			lambdaInstance = new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					funAvmLambda, lambdaVariable, TypeManager::UNIVERSAL,
					offset, Modifier::PROPERTY_PARAMETER_MODIFIER );

			funAvmLambda->setData(offset, lambdaInstance);
		}
		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unexpected LAMBDA VARIABLE for "
						"compileAvmCodeLambda\n" << aCode->toString()
					<< SEND_EXIT;
		}
	}

	funAvmLambda->setExpression( compileArgRvalue(
			aCTX->newCTX(funAvmLambda, aCTX->mRuntimeCtx), aCode->last()) );

	return( bfFunLambda );
//	return( ExpressionConstructor::newCode(
//			OperatorManager::OPERATOR_INVOKE_LAMBDA_APPLY, bfFunLambda) );
}

BFCode AvmcodeLambdaExprCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		AVM_OS_EXIT( FAILED )
				<< "Unexpected LAMBDA EXPRESSION without argument "
					"for compileAvmCodeLambda\n" << aCode->toString()
				<< SEND_EXIT;

		return( BFCode::REF_NULL );
	}

	avm_size_t varCount = aCode->size() - 1;

	AvmLambda * funAvmLambda = new AvmLambda(
			aCTX->mCompileCtx, varCount, AVM_LAMBDA_FUN_NATURE);

	BF bfFunLambda( funAvmLambda );

	BF lambdaVar;
	BF lambdaVarForm;
	Variable * lambdaVariable;
	InstanceOfData * lambdaInstance;

	AvmCode::iterator itArg = aCode->begin();
	for( avm_size_t offset = 0 ; offset < varCount ; ++itArg , ++offset )
	{
		lambdaVar = (*itArg);

		if( lambdaVar.isIdentifier() || lambdaVar.isUfi() ||
				lambdaVar.is< UniFormIdentifier >() )
		{
			lambdaVarForm = BF( lambdaVariable = new Variable(
					const_cast< ObjectElement * >(
							aCTX->mCompileCtx->getAstElement() ),
					TypeManager::UNIVERSAL, lambdaVar.str(), lambdaVar.str()) );
			aCode->set(offset, lambdaVarForm);

			lambdaInstance = new InstanceOfData(
					IPointerDataNature::POINTER_STANDARD_NATURE,
					funAvmLambda, lambdaVariable, TypeManager::UNIVERSAL,
					offset, Modifier::PROPERTY_PARAMETER_MODIFIER );

			funAvmLambda->setData(offset, lambdaInstance);
		}
		else
		{
			AVM_OS_EXIT( FAILED )
					<< "Unexpected LAMBDA VARIABLE for "
						"compileAvmCodeLambda\n" << aCode->toString()
					<< SEND_EXIT;
		}
	}

	BF lambdaCode = AVMCODE_COMPILER.decode_compileStatement(
			aCTX->newCTX(funAvmLambda, aCTX->mRuntimeCtx), aCode->last());

	funAvmLambda->setExpression( lambdaCode );

	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_INVOKE_LAMBDA_APPLY, bfFunLambda) );
}



}
