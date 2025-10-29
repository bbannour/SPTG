/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmcodeGuardCompiler.h"

#include <builder/primitive/AvmcodeCompiler.h>

#include <fml/executable/AvmInstruction.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/type/TypeManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// AVMCODE GUARD COMPILATION
////////////////////////////////////////////////////////////////////////////////

bool AvmcodeGuardCompiler::MAKE_TRIVIAL_ASSIGMENT_FROM_GUARD_ENABLED = false;

BFCode AvmcodeGuardCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first())) );
}


BFCode AvmcodeGuardCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(0);

	if( MAKE_TRIVIAL_ASSIGMENT_FROM_GUARD_ENABLED )
	{
		trivialAssignmentsSequence.clear();

		ExpressionFactory::deduceTrivialAssignmentsFromConjonction(
				aCode->first(), trivialAssignmentsSequence);
		if( trivialAssignmentsSequence.nonempty() )
		{
			bool saveNeedTypeCheckingState = aCTX->mNeedTypeChecking;
			aCTX->mNeedTypeChecking = false;

			optimizeArgStatement(aCTX, trivialAssignmentsSequence);

			aCTX->mNeedTypeChecking = saveNeedTypeCheckingState;

AVM_IF_DEBUG_FLAG2_AND( COMPUTING , STATEMENT ,
	AVM_DEBUG_LEVEL_OR_FLAG(HIGH , TEST_DECISION) )
		trivialAssignmentsSequence.append(
				StatementConstructor::newComment("end<guard>") );
AVM_ENDIF_DEBUG_FLAG2_AND( COMPUTING , STATEMENT )

			return( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					aCode, trivialAssignmentsSequence) );
		}
	}

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE TIMED GUARD COMPILATION
////////////////////////////////////////////////////////////////////////////////

bool AvmcodeTimedGuardCompiler::MAKE_TRIVIAL_ASSIGMENT_FROM_TIMED_GUARD_ENABLED = false;

BFCode AvmcodeTimedGuardCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first())) );
}

BFCode AvmcodeTimedGuardCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(0);

	if( MAKE_TRIVIAL_ASSIGMENT_FROM_TIMED_GUARD_ENABLED )
	{
		trivialAssignmentsSequence.clear();

		ExpressionFactory::deduceTrivialAssignmentsFromConjonction(
				aCode->first(), trivialAssignmentsSequence);

		if( trivialAssignmentsSequence.nonempty() )
		{
			optimizeArgStatement(aCTX, trivialAssignmentsSequence);

	AVM_IF_DEBUG_FLAG2_AND( COMPUTING , STATEMENT ,
		AVM_DEBUG_LEVEL_OR_FLAG(HIGH , TEST_DECISION) )
			trivialAssignmentsSequence.append(
					StatementConstructor::newComment("end<tguard>") );
	AVM_ENDIF_DEBUG_FLAG2_AND( COMPUTING , STATEMENT )

			return( StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					aCode, trivialAssignmentsSequence) );
		}
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
// AVMCODE EVENT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeEventCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	return( StatementConstructor::newCode(aCode->getOperator(),
			compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first())) );
}

BFCode AvmcodeEventCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	optimizeArgExpression(aCTX, aCode, 0);
	argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
	setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

	argsInstruction->computeMainBytecode(0);

	return( aCode );
}



////////////////////////////////////////////////////////////////////////////////
// AVMCODE CHECKSAT COMPILATION
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeChecksatCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasManyOperands() )
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::STRING, aCode->first()),
				compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->second()) ));
	}
	else
	{
		return( StatementConstructor::newCode(aCode->getOperator(),
				compileArgRvalue(aCTX, TypeManager::BOOLEAN, aCode->first())) );
	}
}

BFCode AvmcodeChecksatCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	AvmInstruction * argsInstruction = aCode->genInstruction();

	if( aCode->hasManyOperands() )
	{
		argsInstruction->at(0).dtype = TypeManager::STRING;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());

		optimizeArgExpression(aCTX, aCode, 1);
		argsInstruction->at(1).dtype = TypeManager::BOOLEAN;
		setArgcodeRValue(aCTX, argsInstruction->at(1), aCode->second());
	}
	else
	{
		optimizeArgExpression(aCTX, aCode, 0);
		argsInstruction->at(0).dtype = TypeManager::BOOLEAN;
		setArgcodeRValue(aCTX, argsInstruction->at(0), aCode->first());
	}

	argsInstruction->computeMainBytecode(
			/*context  */ AVM_ARG_STANDARD_CTX,
			/*processor*/ AVM_ARG_STATEMENT_CPU,
			/*operation*/ AVM_ARG_SEVAL_RVALUE,
			/*operand  */ AVM_ARG_STATEMENT_KIND,
			/*dtype    */ TypeManager::BOOLEAN);

	return( aCode );
}




}
