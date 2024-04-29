/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmAssignPrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionSimplifier.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an ASSIGN program
 ***************************************************************************
 */

// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]
bool AvmPrimitive_Assignment::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]

bool AvmPrimitive_Assignment::seval(EvaluationEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.outED = ENV.mARG->outED;
		ENV.outVAL = ENV.mARG->at(1);

		return( true );
	}

	return( false );
}


/**
 ***************************************************************************
 * execution of an ASSIGN RDECR program
 ***************************************************************************
 */

// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]
bool AvmPrimitive_AssignmentAfter::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


// lvalue =: rvalue;  ==>  [ lvalue , rvalue ]
bool AvmPrimitive_AssignmentAfter::seval(EvaluationEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:> " << ENV.mARG->at(2).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	ENV.outVAL = ENV.mARG->at(1);

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(2)) )
	{
		ENV.outED = ENV.mARG->outED;

		return( true );
	}

	return( false );
}



/**
 ***************************************************************************
 * execution of an ASSIGN RDECR program
 ***************************************************************************
 */

// lvalue =: op rvalue;  ==>  [ lvalue , (VAL[lvalue] op rvalue) ]
bool AvmPrimitive_AssignmentOpAfter::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
//
		return( true );
	}

	return( false );
}


// lvalue =: op rvalue;  ==>  [ lvalue , VAL[lvalue] , (VAL[lvalue] op rvalue) ]
bool AvmPrimitive_AssignmentOpAfter::seval(EvaluationEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:> " << ENV.mARG->at(2).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	ENV.outVAL = ENV.mARG->at(1);

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(2)) )
	{
		ENV.outED = ENV.mARG->outED;

		return( true );
	}

	return( false );
}



/**
 ***************************************************************************
 * execution of an ASSIGN REFERENCE program
 ***************************************************************************
 */
bool AvmPrimitive_AssignmentRef::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:lvalue>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_AssignmentRef::seval(EvaluationEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:lvalue>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.outED = ENV.mARG->outED;
		ENV.outVAL = ENV.mARG->at(1);

		return( true );
	}

	return( false );
}



/**
 ***************************************************************************
 * execution of an ASSIGN MACRO program
 ***************************************************************************
 */
bool AvmPrimitive_AssignmentMacro::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_AssignmentMacro::seval(EvaluationEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue>> " << ENV.mARG->at(1).str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), ENV.mARG->at(1)) )
	{
		ENV.outED = ENV.mARG->outED;
		ENV.outVAL = ENV.mARG->at(1);

		return( true );
	}

	return( false );
}




/**
 ***************************************************************************
 * execution of an NEW FRESH program
 ***************************************************************************
 */
bool AvmPrimitive_AssignNewFresh::run(ExecutionEnvironment & ENV)
{
	BFList paramList;
	BF aNewSymbolicConstant = ENV.createNewFreshParam(ENV.mARG->outED.getRID(),
			ENV.mARG->at(0).to< InstanceOfData >(), paramList );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << aNewSymbolicConstant.str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), aNewSymbolicConstant) )
	{
		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_ASSIGN_NEWFRESH,
								ENV.mARG->at(0), aNewSymbolicConstant))));

		ENV.mARG->outED.appendParameters( paramList );

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_AssignNewFresh::seval(EvaluationEnvironment & ENV)
{
	BFList paramList;
	BF aNewSymbolicConstant = ENV.createNewFreshParam(ENV.mARG->outED.getRID(),
			ENV.mARG->at(0).to< InstanceOfData >(), paramList );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << aNewSymbolicConstant.str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), aNewSymbolicConstant) )
	{
		ENV.outVAL = aNewSymbolicConstant;

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_ASSIGN_NEWFRESH,
								ENV.mARG->at(0), aNewSymbolicConstant))));

		ENV.mARG->outED.appendParameters( paramList );

		return( true );
	}

	return( false );
}



/**
 ***************************************************************************
 * execution of an RESET program
 ***************************************************************************
 */
bool AvmPrimitive_AssignReset::run(ExecutionEnvironment & ENV)
{
	BFList paramList;
//	BF aNewSymbolicConstant = ExpressionConstant::INTEGER_ZERO;

	const BaseTypeSpecifier & typeSpecifier =
			ENV.mARG->at(0).to< InstanceOfData >().getTypeSpecifier();

	BF aNewSymbolicConstant = typeSpecifier.hasDefaultValue()
			? typeSpecifier.getDefaultValue()
			: ENV.createNewFreshParam(ENV.mARG->outED.getRID(),
			ENV.mARG->at(0).to< InstanceOfData >(), paramList );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl
			<< "rvalue:>> " << aNewSymbolicConstant.str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), aNewSymbolicConstant) )
	{
		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_ASSIGN_RESET,
								ENV.mARG->at(0), aNewSymbolicConstant))));

		ENV.mARG->outED.appendParameters( paramList );

		ENV.appendOutput( ENV.mARG->outED );

		return( true );
	}

	return( false );
}


bool AvmPrimitive_AssignReset::seval(EvaluationEnvironment & ENV)
{
	BFList paramList;
	BF aNewSymbolicConstant = ENV.createNewFreshParam(ENV.mARG->outED.getRID(),
			ENV.mARG->at(0).to< InstanceOfData >(), paramList );

AVM_IF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )
	AVM_OS_TRACE << "lvalue:>> "
			<< str_header( ENV.mARG->at(0).to< InstanceOfData >() )
			<< std::endl<< "rvalue:>> " << aNewSymbolicConstant.str()
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_ASSIGNMENT )

	if( ENV.setRvalue(ENV.mARG->outED,
			ENV.mARG->at(0).to< InstanceOfData >(), aNewSymbolicConstant) )
	{
		ENV.outVAL = aNewSymbolicConstant;

		ExecutionDataFactory::appendIOElementTrace(ENV.mARG->outED,
				BF(new ExecutionConfiguration(ENV.mARG->outED.getRID(),
						StatementConstructor::newCode(
								OperatorManager::OPERATOR_ASSIGN_RESET,
								ENV.mARG->at(0), aNewSymbolicConstant))));

		ENV.mARG->outED.appendParameters( paramList );

		return( true );
	}

	return( false );
}



}
