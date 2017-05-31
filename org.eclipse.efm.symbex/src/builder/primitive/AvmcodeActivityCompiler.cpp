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

#include "AvmcodeActivityCompiler.h"

#include <collection/Typedef.h>

#include <builder/primitive/AvmcodeSequenceCompiler.h>
#include <builder/primitive/AvmcodeUfiCastExpressionCompiler.h>

#include <fml/common/ObjectElement.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementTypeChecker.h>

#include <fml/operator/OperatorManager.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE ACTIVITY STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeActivityStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
		return( aCode );
	}
	else
	{
		return( compileStatementParams(aCTX, aCode) );
	}
}

BFCode AvmcodeActivityStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasInstruction() )
	{
		return( aCode );
	}

	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::MACHINE;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	if( aCode->populated() )
	{
		AvmCode::iterator itParam = aCode->begin();
		AvmCode::iterator itEndParam = aCode->end();
		avm_offset_t offset = 1;
		for( ++itParam ; itParam != itEndParam ; ++itParam , ++offset )
		{
			optimizeArgExpression(aCTX, aCode, offset);

			setArgcodeParamValue(aCTX, argsInstruction->at(offset), (*itParam), false);
		}
	}

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype     */ argsInstruction->at(0).dtype);

	return( aCode );
}


BFCode AvmcodeActivityStatementCompiler::compileStatementParams(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode( aCode->getOperator() );

	if( aCode->empty() )
	{
		return( newCode );
	}

	AvmCode::iterator itArg = aCode->begin();

	newCode->append( compileArgRvalue(aCTX, TypeManager::MACHINE, (*itArg)) );

	AvmCode::iterator itEndArg = aCode->end();
	for( ++itArg ; itArg != itEndArg ; ++itArg )
	{
		switch( (*itArg).classKind() )
		{
			case FORM_AVMCODE_KIND:
			{
				const BFCode & argCode = (*itArg).bfCode();
				if( aCode->populated() &&
						StatementTypeChecker::isAssign( argCode ) &&
						newCode->first().is< InstanceOfMachine >() )
				{
					ExecutableForm * execInstance = newCode->first().
							to_ptr< InstanceOfMachine >()->getExecutable();

					if( argCode->populated() )
					{
						newCode->append( StatementConstructor::newCode(
							argCode->getOperator(),
							compileArgLvalue( aCTX->newCTX(execInstance,
									Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER),
								argCode->first()),
							compileArgRvalue( aCTX->newCTX(
									Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER),
								argCode->second())) );
					}
					else
					{
						newCode->append( StatementConstructor::newCode(
							argCode->getOperator(),	compileArgLvalue(
								aCTX->newCTX(execInstance,
										Modifier::PROPERTY_PUBLIC_VOLATILE_MODIFIER),
								argCode->first())) );
					}
				}
				else
				{
					newCode->append(
							AVMCODE_COMPILER.compileExpression(aCTX, argCode) );
				}

				break;
			}

			default:
			{
				newCode->append( compileArgRvalue(aCTX, (*itArg)) );

				break;
			}
		}
	}

	return( newCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE CONTEXT SWITCHER STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeContextSwitcherStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() != 2 )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Expected CONTEXT SWITCHER with one running "
					"machine and a statement as parameter !!!"
				<< SEND_EXIT;
	}

	BF ctxMachine = compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first() );

	if( ctxMachine.is< InstanceOfMachine >() )
	{
		aCTX = aCTX->newCTX(
				//ctxMachine.to_ptr< InstanceOfMachine >()->getExecutable(),
				ctxMachine.to_ptr< InstanceOfMachine >()->getExecutable() );
	}

	return( StatementConstructor::newCode( aCode->getOperator(), ctxMachine,
			compileStatementCode(aCTX, aCode->second().bfCode())) );
}


BFCode AvmcodeContextSwitcherStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::MACHINE;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	if( aCode->first().is< InstanceOfMachine >() )
	{
		aCTX = aCTX->newCTX(aCode->first().
				to_ptr< InstanceOfMachine >()->getExecutable() );
	}

	optimizeArgStatement(aCTX, aCode, 1);
	argsInstruction->at(1).dtype = TypeManager::UNIVERSAL;
	setArgcodeStatement(aCTX, argsInstruction->at(1), aCode->second(), false);

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype     */ argsInstruction->at(0).dtype);

	return( aCode );
}

////////////////////////////////////////////////////////////////////////////////
// AVMCODE IENABLE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeIEnableStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected IENABLE STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeIEnableStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnIEnable() )
		{
			if( aCTX->isInlineEnable(anExecutable) )
			{
				BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
						aCTX->newCTX(anExecutable), anExecutable->getOnIEnable() );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
				return( StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

						StatementConstructor::newComment(
								"<ienable> " + anExecutable->getFullyQualifiedNameID()),

						optiCode,

						StatementConstructor::newComment(
								"end<ienable> " + anExecutable->getFullyQualifiedNameID()) ));

AVM_ELSE

				return( optiCode );

AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			}
			else
			{
				return( AvmcodeActivityStatementCompiler::
						optimizeStatement(aCTX, aCode) );
			}
		}
		else
		{
			return( StatementConstructor::newComment(
					"nop<ienable> " + anExecutable->getFullyQualifiedNameID() ));
		}
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ENABLE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeEnableStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ENABLE STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeEnableStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnEnable() )
		{
			if( aCTX->isInlineEnable(anExecutable) )
			{
				BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
						aCTX->newCTX(anExecutable), anExecutable->getOnEnable() );

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
				return( StatementConstructor::newCodeFlatMiddle(
						OperatorManager::OPERATOR_ATOMIC_SEQUENCE,

						StatementConstructor::newComment(
								"begin<enable> " + anExecutable->getFullyQualifiedNameID() ),

						optiCode,

						StatementConstructor::newComment(
								"end<enable> " + anExecutable->getFullyQualifiedNameID()) ));

AVM_ELSE

				return( optiCode );

AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
			}
			else
			{
				return( AvmcodeActivityStatementCompiler::
						optimizeStatement(aCTX, aCode) );
			}
		}
		else
		{
			return( StatementConstructor::newComment(
					"nop<enable> " + anExecutable->getFullyQualifiedNameID() ));
		}
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE IDISABLE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeIDisableStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode( aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected IDISABLE STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeIDisableStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnIDisable() )
		{
//			BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
//					aCTX->newCTX(anExecutable), anExecutable->getOnIDisable() );
//
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//			return( StatementConstructor::newCodeFlatMiddle(
//					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
//
//					StatementConstructor::newComment(
//							"begin<idisable> " + anExecutable->getFullyQualifiedNameID()),
//
//					optiCode,
//
//					StatementConstructor::newComment(
//							"end<idisable> " + anExecutable->getFullyQualifiedNameID()) ));
//_AVM_ELSE_
//
//			return( optiCode );
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}
		else
		{
			return( StatementConstructor::newComment(
					"nop<idisable> " + anExecutable->getFullyQualifiedNameID()) );
		}
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE DISABLE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeDisableStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		if( ExpressionTypeChecker::isInteger(aCode->first()) )
		{
			return( AVMCODE_COMPILER.compileStatement(aCTX,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_SELVES,
							aCode->first() )));
		}

		return( StatementConstructor::newCode( aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );

	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected DISABLE STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeDisableStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnDisable() )
		{
//			BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
//					aCTX->newCTX(anExecutable), anExecutable->getOnDisable() );
//
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//			return( StatementConstructor::newCodeFlatMiddle(
//					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
//
//					StatementConstructor::newComment(
//							"begin<disable> " + anExecutable->getFullyQualifiedNameID()),
//
//					optiCode,
//
//					StatementConstructor::newComment(
//							"end<disable> " + anExecutable->getFullyQualifiedNameID()) ));
//_AVM_ELSE_
//
//			return( optiCode );
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}
		else if( aCode->first() == ExecutableLib::MACHINE_SELF )
		{
			return( StatementConstructor::newCode(
					OperatorManager::OPERATOR_DISABLE_SELF) );
		}
		else
		{
			return( AvmcodeActivityStatementCompiler::optimizeStatement(
					aCTX, StatementConstructor::newCode(
					OperatorManager::OPERATOR_DISABLE_SET, aCode->first() )));
		}
	}
	else if( aCode->first() == ExecutableLib::MACHINE_SELF )
	{
		return( StatementConstructor::newCode(
				OperatorManager::OPERATOR_DISABLE_SELF) );
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE DISABLE#SELVES STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeDisableSelvesStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->singleton() )
	{
		if( ExpressionTypeChecker::isInteger(aCode->first()) )
		{
			if( aCode->first().isWeakInteger() &&
					(aCode->first().toInteger() < 0) )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected DISABLE#SELVES STATEMENT with "
							"a negative integer as parameter !!!"
						<< SEND_EXIT;

				return( StatementConstructor::newCode(
						aCode->getOperator(),
						ExpressionConstructor::newUInteger(
								(- aCode->first().toInteger()) ) ) );
			}
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected DISABLE#SELVES STATEMENT with "
					"only an unsigned integer as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}

BFCode AvmcodeDisableSelvesStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode;

	if( aCode->first().isWeakInteger() )
	{
		ExecutableForm * anExecutable = aCTX->mCompileCtx->getExecutable();
		avm_integer_t interLevel = 0;

		optCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE);

		avm_integer_t disableLevel = aCode->first().toInteger();
		for( avm_integer_t level = disableLevel ;
				(level > 0) && (anExecutable != NULL) ; --level )
		{
			if( anExecutable->hasOnIDisable() )
			{
				if( interLevel > 1 )
				{
					optCode->append( StatementConstructor::newOptiNopCode(
							OperatorManager::OPERATOR_DISABLE_SELVES,
							ExpressionConstructor::newUInteger(interLevel),
							AVM_ARG_BUILTIN_KIND) );
				}
				else if( interLevel == 1 )
				{
					optCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_DISABLE_SELF) );
				}

				optCode->appendFlat( anExecutable->getOnIDisable() );

				interLevel = 0;
			}
			else
			{
				interLevel = interLevel + 1;
			}

			anExecutable = anExecutable->getExecutableContainer();
		}

		if( interLevel != disableLevel )
		{
			if( interLevel > 1 )
			{
				optCode->append( StatementConstructor::newOptiNopCode(
						OperatorManager::OPERATOR_DISABLE_SELVES,
						ExpressionConstructor::newUInteger(interLevel),
						AVM_ARG_BUILTIN_KIND) );
			}
			else if( interLevel == 1 )
			{
				optCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_DISABLE_SELF) );
			}

			return( AvmcodeStrongSequenceCompiler::atomizeSequence(optCode) );
		}
		else
		{
			AvmInstruction * argsInstruction = aCode->genInstruction();

			argsInstruction->set( 0,
					/*operation*/ AVM_ARG_NOP_RVALUE,
					/*operand  */ AVM_ARG_BUILTIN_KIND,
					/*dtype    */ TypeManager::INTEGER );

			argsInstruction->computeMainBytecode(0);

			return( aCode );
		}
	}
	else
	{
		AvmInstruction * argsInstruction = aCode->genInstruction();

		optimizeArgExpression(aCTX, aCode, 0);
		argsInstruction->at(0).dtype = TypeManager::INTEGER;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

		argsInstruction->computeMainBytecode(0);

		return( aCode );
	}
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE IABORT STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeIAbortStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected IABORT STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeIAbortStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnIAbort() )
		{
//			BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
//					aCTX->newCTX(anExecutable), anExecutable->getOnIAbort() );
//
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//			return(StatementConstructor::newCodeFlatMiddle(
//					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
//
//					StatementConstructor::newComment(
//							"begin<iabort> " + anExecutable->getFullyQualifiedNameID()),
//
//					optiCode,
//
//					StatementConstructor::newComment(
//							"end<iabort> " + anExecutable->getFullyQualifiedNameID()) ));
//_AVM_ELSE_
//
//			return( optiCode );
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}
		else
		{
			return( StatementConstructor::newComment(
					"nop<iabort> " + anExecutable->getFullyQualifiedNameID()) );
		}
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE ABORT STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeAbortStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first())) );
	}
	else if( aCode->nonempty() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ABORT STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeAbortStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());

	if( anExecutable != NULL )
	{
		if( anExecutable->hasOnAbort() )
		{
//			BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
//					aCTX->newCTX(anExecutable), anExecutable->getOnAbort() );
//
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//			return( StatementConstructor::newCodeFlatMiddle(
//					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
//
//					StatementConstructor::newComment(
//							"begin<abort> " + anExecutable->getFullyQualifiedNameID() ),
//
//					optiCode,
//
//					StatementConstructor::newComment(
//							"end<abort> " + anExecutable->getFullyQualifiedNameID()) ));
//_AVM_ELSE_
//
//			return( optiCode );
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
		}
		else if( aCode->first() == ExecutableLib::MACHINE_SELF )
		{
			return( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ABORT_SELF) );
		}
		else
		{
			return( AvmcodeActivityStatementCompiler::optimizeStatement(
					aCTX, StatementConstructor::newCode(
							OperatorManager::OPERATOR_ABORT_SET,
							aCode->first() )));
		}
	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}




////////////////////////////////////////////////////////////////////////////////
// AVMCODE ABORT#SELVES STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeAbortSelvesStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->singleton() )
	{
		if( ExpressionTypeChecker::isInteger(aCode->first()) )
		{
			if( aCode->first().isWeakInteger() &&
					(aCode->first().toInteger() < 0) )
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "Unexpected ABORT#SELVES STATEMENT with "
							"a negative integer as parameter !!!"
						<< SEND_EXIT;

				return( StatementConstructor::newCode(
						aCode->getOperator(),
						ExpressionConstructor::newUInteger(
								(- aCode->first().toInteger()) ) ) );
			}
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ABORT#SELVES STATEMENT with "
					"only an unsigned integer as parameter !!!"
				<< SEND_EXIT;
	}

	return( aCode );
}


BFCode AvmcodeAbortSelvesStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->first().isWeakInteger() )
	{
		ExecutableForm * anExecutable = aCTX->mCompileCtx->getExecutable();
		avm_integer_t interLevel = 0;

		BFCode optCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_ATOMIC_SEQUENCE);

		avm_integer_t abortLevel = aCode->first().toInteger();
		for( avm_integer_t level = abortLevel ;
				(level > 0) && (anExecutable != NULL) ; --level )
		{
			if( anExecutable->hasOnIAbort() )
			{
				if( interLevel > 1 )
				{
					optCode->append( StatementConstructor::newOptiNopCode(
							OperatorManager::OPERATOR_ABORT_SELVES,
							ExpressionConstructor::newUInteger(interLevel),
							AVM_ARG_BUILTIN_KIND) );
				}
				else if( interLevel == 1 )
				{
					optCode->append( StatementConstructor::newCode(
							OperatorManager::OPERATOR_ABORT_SELF) );
				}

				optCode->appendFlat( anExecutable->getOnIDisable() );

				interLevel = 0;
			}
			else
			{
				interLevel = interLevel + 1;
			}

			anExecutable = anExecutable->getExecutableContainer();
		}

		if( interLevel != abortLevel )
		{
			if( interLevel > 1 )
			{
				optCode->append( StatementConstructor::newOptiNopCode(
						OperatorManager::OPERATOR_ABORT_SELVES,
						ExpressionConstructor::newUInteger(interLevel),
						AVM_ARG_BUILTIN_KIND) );
			}
			else if( interLevel == 1 )
			{
				optCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ABORT_SELF) );
			}

			return( AvmcodeStrongSequenceCompiler::atomizeSequence(optCode) );
		}
		else
		{
			AvmInstruction * argsInstruction = aCode->genInstruction();

			argsInstruction->set( 0,
					/*operation*/ AVM_ARG_NOP_RVALUE,
					/*operand  */ AVM_ARG_BUILTIN_KIND,
					/*dtype    */ TypeManager::INTEGER );

			argsInstruction->computeMainBytecode(0);

			return( aCode );
		}
	}
	else
	{
		AvmInstruction * argsInstruction = aCode->genInstruction();

		optimizeArgExpression(aCTX, aCode, 0);
		argsInstruction->at(0).dtype = TypeManager::INTEGER;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

		argsInstruction->computeMainBytecode(0);

		return( aCode );
	}
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE FORK STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeForkStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() < 2 )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected FORK STATEMENT with less "
					"than 2 running machines as parameters !!!"
				<< SEND_EXIT;

		return( aCode );
	}
	else
	{
		return( AbstractAvmcodeCompiler::compileStatement(aCTX, aCode) );
	}
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE JOIN STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeJoinStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected JOIN STATEMENT without "
					"running machines as parameters !!!"
				<< SEND_EXIT;

		return( aCode );
	}
	else if( aCode->singleton() )
	{
		return( StatementConstructor::newCode( aCode->getOperator(),
				compileArgRvalue(aCTX, aCode->first()) ) );
	}
	else
	{

		return( compileStatementParams(aCTX, aCode) );
	}
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE GOTO STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeGotoStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected GOTO STATEMENT without "
					"one running machine as target !!!"
				<< SEND_EXIT;

		return( aCode );
	}
	else
	{
		BF gotoTarget = AVMCODE_COMPILER.decode_compileVariableMachine(
				aCTX, aCode->first());

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( gotoTarget.is< InstanceOfMachine >() )
				<< "Unexpected GOTO machine target:>\n" << aCode.str()
				<< SEND_EXIT;

		BFCode flowStatement;
		if( aCode->populated() && gotoTarget.is< InstanceOfMachine >() )
		{
			flowStatement = AVMCODE_COMPILER.decode_compileStatement(
					gotoTarget.to_ptr< InstanceOfMachine >()->getExecutable(),
					aCode->second());

			AVM_OS_ASSERT_FATAL_ERROR_EXIT( flowStatement.valid() )
					<< "Unexpected GOTO flow statement:>\n" << aCode.str()
					<< SEND_EXIT;
		}


		const Machine * source =
				aCTX->mCompileCtx->getExecutable()->getAstMachine();
		const Machine * target =
				gotoTarget.to_ptr< InstanceOfMachine >()->getAstMachine();

		const Machine * lcaMachine = source->LCRA(target);
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( lcaMachine )
				<< "Unexpected a <null> LCA( "
				<< source->getFullyQualifiedNameID() << " , "
				<< target->getFullyQualifiedNameID() << " )"
				<< SEND_EXIT;

		BFCode disableCode( OperatorManager::OPERATOR_DISABLE_INVOKE );
		BFCode enableCode ( OperatorManager::OPERATOR_ENABLE_INVOKE  );
		BFList listOfEnableTarget;

		if( (source != lcaMachine)
			&& (source->getContainerMachine() != lcaMachine) )
		{
			avm_uinteger_t disableLevel = 1;

			const Machine * containerOfSource = source->getContainerMachine();
			for( ; containerOfSource != lcaMachine ; ++disableLevel )
			{
				containerOfSource = containerOfSource->getContainerMachine();
			}

			disableCode = StatementConstructor::newOptiNopCode(
					OperatorManager::OPERATOR_DISABLE_SELVES,
					ExpressionConstructor::newUInteger(disableLevel),
					AVM_ARG_BUILTIN_KIND);
		}
		if( target != lcaMachine )
		{
			const Machine * containerOfMachine = target;
			for( ; containerOfMachine != lcaMachine ;
				containerOfMachine = containerOfMachine->getContainerMachine() )
			{
				listOfEnableTarget.push_front(
					getSymbolTable().searchInstanceStatic(containerOfMachine) );
			}
			enableCode.append( listOfEnableTarget );

			if( flowStatement.valid() )
			{
				enableCode = AvmcodeStrongSequenceCompiler::atomizeSequence(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_SEQUENCE,
								enableCode, flowStatement) );
			}
		}


		if( source != lcaMachine ) // for disable self
		{
			if( enableCode->nonempty() )
			{
				return( AvmcodeStrongSequenceCompiler::atomizeSequence(
						StatementConstructor::newCodeFlat(
								OperatorManager::OPERATOR_SEQUENCE,
								disableCode, enableCode) ));
			}
			else
			{
				return( disableCode );
			}
		}
		else
		{
			return( enableCode );
		}

//		return( compileStatementParams(aCTX, aCode) );
	}
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE SCHEDULE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeRtcStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
		return( aCode );
	}
	else
	{
		return( AvmcodeActivityStatementCompiler::
				compileStatement(aCTX, aCode) );
	}
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE SCHEDULE#INVOKE STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeScheduleStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
		return( aCode );
	}
	else
	{
		return( AvmcodeActivityStatementCompiler::
				compileStatement(aCTX, aCode) );
	}
}


BFCode AvmcodeScheduleStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->empty() )
	{
		aCode->append( ExecutableLib::MACHINE_SELF );
	}

//	ExecutableForm * anExecutable = getExecutableMachine(aCTX, aCode->first());
//
//	if( (anExecutable != NULL) && anExecutable->hasOnSchedule() &&
//			anExecutable->isInlinableSchedule() )
//	{
//		BFCode optiCode = AVMCODE_COMPILER.optimizeStatement(
//				aCTX->newCTX(anExecutable), anExecutable->getOnSchedule() );
//
//AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//		return( StatementConstructor::newCodeFlatMiddle(
//				OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
//
//				StatementConstructor::newComment(
//						"begin<schedule> " + anExecutable->getFullyQualifiedNameID() ),
//
//				optiCode,
//
//				StatementConstructor::newComment(
//						"end<schedule> " + anExecutable->getFullyQualifiedNameID()) ));
//
//AVM_ELSE
//
//		return( optiCode );
//
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , COMPUTING , STATEMENT )
//	}

	return( AvmcodeActivityStatementCompiler::optimizeStatement(aCTX, aCode) );
}




////////////////////////////////////////////////////////////////////////////////
// AVMCODE SCHEDULE#IN STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeScheduleInStatementCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->size() == 2 )
	{
		BF machine = compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->second());

		if( machine.is< InstanceOfMachine >() )
		{
			aCTX = aCTX->newCTX(
					machine.to_ptr< InstanceOfMachine >()->getExecutable() );
		}
		BF submachine = compileArgRvalue(aCTX, TypeManager::MACHINE, aCode->first());

		BFCode newCode( aCode->getOperator(), submachine, machine);

		return( newCode );
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ENABLE#SET STATEMENT with more "
					"than one running machine as parameter !!!"
				<< SEND_EXIT;

		return( aCode );
	}
}


BF AvmcodeScheduleInStatementCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	argsInstruction->at(0).dtype = TypeManager::MACHINE;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->at(1).dtype = argsInstruction->at(0).dtype;
	setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_RETURN_CTX,
			/*processor*/ AVM_ARG_MEMORY_MACHINE_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_EXPRESSION_KIND,
			/*dtype    */ TypeManager::MACHINE);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE INPUT_ENABLED STATEMENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeInputEnabledStatementCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode newCode( aCode->getOperator(),
			AbstractAvmcodeCompiler::compileStatementCode(aCTX,
					aCode->first().bfCode()) );

	return( newCode );
}


BFCode AvmcodeInputEnabledStatementCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	BFCode optCode( aCode->getOperator() );

	optCode->append( AVMCODE_COMPILER.optimizeStatement(aCTX,
			aCode->first().bfCode() ));

	return( optCode );
}




}

