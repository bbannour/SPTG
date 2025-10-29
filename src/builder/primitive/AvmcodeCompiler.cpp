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

#include "AvmcodeCompiler.h"

#include <builder/compiler/BaseCompiler.h>
#include <builder/compiler/BaseCompilerTable.h>

#include <builder/primitive/AbstractAvmcodeCompiler.h>
#include <builder/primitive/AvmcodeActivityCompiler.h>
#include <builder/primitive/AvmcodeAssignCompiler.h>
#include <builder/primitive/AvmcodeCommunicationCompiler.h>
#include <builder/primitive/AvmcodeContainerCompiler.h>
#include <builder/primitive/AvmcodeCtorExpressionCompiler.h>
#include <builder/primitive/AvmcodeExpressionCompiler.h>
#include <builder/primitive/AvmcodeGinacCompiler.h>
#include <builder/primitive/AvmcodeGuardCompiler.h>
#include <builder/primitive/AvmcodeInvokeCompiler.h>
#include <builder/primitive/AvmcodeIteCompiler.h>
#include <builder/primitive/AvmcodeJumpCompiler.h>
#include <builder/primitive/AvmcodeLambdaCompiler.h>
#include <builder/primitive/AvmcodeLookupExprCompiler.h>
#include <builder/primitive/AvmcodeLoopCompiler.h>
#include <builder/primitive/AvmcodeMachineStatusCompiler.h>
#include <builder/primitive/AvmcodeMathFunctionCompiler.h>
#include <builder/primitive/AvmcodeMetaStatementCompiler.h>
#include <builder/primitive/AvmcodeQueueCompiler.h>
#include <builder/primitive/AvmcodeSchedulingCompiler.h>
#include <builder/primitive/AvmcodeSequenceCompiler.h>
#include <builder/primitive/AvmcodeUfiCastExpressionCompiler.h>
#include <builder/primitive/AvmcodeVariableStatusCompiler.h>

#include <fml/common/SpecifierElement.h>

#include <fml/executable/AvmProgram.h>
#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinContainer.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementFactory.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/DataType.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/Variable.h>

#include <fml/workflow/UniFormIdentifier.h>

#include <sew/Configuration.h>


namespace sep
{


#define NEW_COMPILER( OP_AC )  \
	( AVMCODE_COMPILER_TABLE_FOR_DESTROY.push_back( new OP_AC( *this ) ) ,  \
	AVMCODE_COMPILER_TABLE_FOR_DESTROY.back() )


#define OPCODE_COMPILER( OP_ID )   \
	AVMCODE_COMPILER_TABLE[ OperatorManager::OPERATOR_##OP_ID->getOffset() ]



/**
 * DESTRUCTOR
 */
AvmcodeCompiler::~AvmcodeCompiler()
{
	AVMCODE_COMPILER_TABLE.clear();

	std::vector< AbstractAvmcodeCompiler * >::iterator it =
			AVMCODE_COMPILER_TABLE_FOR_DESTROY.begin();
	std::vector< AbstractAvmcodeCompiler * >::iterator endIt =
			AVMCODE_COMPILER_TABLE_FOR_DESTROY.end();
	for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
	{
		delete( *it );
	}

	delete( UFI_EXPRESSION_COMPILER );

	AVMCODE_COMPILER_TABLE_FOR_DESTROY.clear();
}


/*
 * GETTER
 * theSymbolTable
 */
SymbolTable & AvmcodeCompiler::getSymbolTable()
{
	return( mCompilerTable.getSymbolTable() );
}


/**
 * CONFIGURE
 */
bool AvmcodeCompiler::configure()
{
	DEFAULT_AVMCODE_COMPILER =NEW_COMPILER( AbstractAvmcodeCompiler );

	NOTHING_AVMCODE_COMPILER =NEW_COMPILER( AvmcodeNothingCompiler );

	UNARY_ARITHMETIC_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeUnaryArithmeticExpressionALUCompiler );
	BINARY_ARITHMETIC_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeBinaryArithmeticExpressionALUCompiler );
	ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeAssociativeArithmeticExpressionALUCompiler );

	UNARY_BITWISE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeUnaryBitwiseExpressionCompiler );
	BINARY_BITWISE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeBinaryBitwiseExpressionCompiler );
	ASSOCIATIVE_BITWISE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeAssociativeBitwiseExpressionCompiler );

	UNARY_PREDICATE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeUnaryPredicateExpressionCompiler );
	BINARY_PREDICATE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeBinaryPredicateExpressionCompiler );
	QUANTIFIED_PREDICATE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeQuantifiedPredicateExpressionCompiler );
	ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeAssociativePredicateExpressionCompiler );

	RELATIONAL_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeRelationalExpressionCompiler );

	UNARY_STRING_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeUnaryStringExpressionCompiler );
	BINARY_STRING_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeBinaryStringExpressionCompiler );
	ASSOCIATIVE_STRING_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeAssociativeStringExpressionCompiler );

	LOOKUP_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeLookupExpressionCompiler );

	MACHINE_STATUS_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeMachineStatusExpressionCompiler );

	MATH_FUNCTION_COMPILER =
			NEW_COMPILER( AvmcodeMathFunctionCompiler );

	UFI_EXPRESSION_COMPILER =
			new AvmcodeUfiExpressionCompiler( *this );

	VARIABLE_STATUS_EXPRESSION_COMPILER =
			NEW_COMPILER( AvmcodeVariableStatusExpressionCompiler );


	ACTIVITY_STATEMENT_COMPILER =
			NEW_COMPILER( AvmcodeActivityStatementCompiler );

	SCHEDULING_STATEMENT_COMPILER =
			NEW_COMPILER( AvmcodeSchedulingCompiler );

	SEQUENCE_STATEMENT_COMPILER =
			NEW_COMPILER( AvmcodeSequenceCompiler );

	ITE_STATEMENT_COMPILER =
			NEW_COMPILER( AvmcodeIteCompiler );


	UNARY_CONTAINER_STATEMENT =
			NEW_COMPILER( AvmcodeUnaryContainerStatementCompiler );

	UNARY_WRITE_CONTAINER_STATEMENT =
			NEW_COMPILER( AvmcodeUnaryWriteContainerStatementCompiler );

	BINARY_CONTAINER_STATEMENT =
			NEW_COMPILER( AvmcodeBinaryContainerStatementCompiler );

	BINARY_WRITE_CONTAINER_STATEMENT =
			NEW_COMPILER( AvmcodeBinaryWriteContainerStatementCompiler );


	//DEFAULT_AVMCODE_COMPILER);
	AVMCODE_COMPILER_TABLE.resize(
			OperatorManager::TABLE_OF_OPERATOR.size(),
			DEFAULT_AVMCODE_COMPILER );

	if( not configureOther() )
	{
		return( false );
	}

	if( not configureMeta() )
	{
		return( false );
	}

	if( not configureLambdaPrimitive() )
	{
		return( false );
	}

	if( not configureActivityPrimitive() )
	{
		return( false );
	}

	if( not configureStatusPrimitive() )
	{
		return( false );
	}

	if( not configureSchedulingPrimitive() )
	{
		return( false );
	}
	if( not configureBasicPrimitive() )
	{
		return( false );
	}

	if( not configureArithmeticPrimitive() )
	{
		return( false );
	}
	if( not configureBitwisePrimitive() )
	{
		return( false );
	}
	if( not configureLogicPrimitive() )
	{
		return( false );
	}

	if( not configureLookupPrimitive() )
	{
		return( false );
	}
	if( not configureMathematicPrimitive() )
	{
		return( false );
	}

	if( not configureStringCollectionPrimitive() )
	{
		return( false );
	}

	if( not configureIoltPrimitive() )
	{
		return( false );
	}

	return( true );
}


bool AvmcodeCompiler::configureOther()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM UFI STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( UFI ) = UFI_EXPRESSION_COMPILER;

	////////////////////////////////////////////////////////////////////////////
	// AVM CAST STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( CTOR ) = NEW_COMPILER( AvmcodeCtorExpressionCompiler );

	////////////////////////////////////////////////////////////////////////////
	// AVM GINAC EXPRESSION & STATEMENT
	////////////////////////////////////////////////////////////////////////////
//	mGinacPrimitive = NEW_COMPILER( AbstractAvmcodeCompiler );


	return( true );
}


bool AvmcodeCompiler::configureMeta()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM NOP STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( NOP ) = NOTHING_AVMCODE_COMPILER;

	////////////////////////////////////////////////////////////////////////////
	// AVM META STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( INFORMAL  ) = NEW_COMPILER( AvmcodeInformalExpressionCompiler );

	OPCODE_COMPILER( TRACE     ) = NEW_COMPILER( AvmcodeTraceExpressionCompiler );

	OPCODE_COMPILER( DEBUG     ) = NEW_COMPILER( AvmcodeDebugExpressionCompiler );

	OPCODE_COMPILER( COMMENT   ) = NEW_COMPILER( AvmcodeCommentExpressionCompiler );

	OPCODE_COMPILER( QUOTE     ) = DEFAULT_AVMCODE_COMPILER;

	OPCODE_COMPILER( META_EVAL ) = NEW_COMPILER( AvmcodeMetaEvalStatementCompiler );
	OPCODE_COMPILER( META_RUN  ) = NEW_COMPILER( AvmcodeMetaRunStatementCompiler );


	return( true );
}


bool AvmcodeCompiler::configureLambdaPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// LAMBDA STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( APPLY  ) = NEW_COMPILER( AvmcodeLambdaApplyCompiler );

	OPCODE_COMPILER( LAMBDA ) = NEW_COMPILER( AvmcodeLambdaExprCompiler );

	////////////////////////////////////////////////////////////////////////////
	// LET STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( LET ) = NEW_COMPILER( AvmcodeLambdaLetCompiler );


	return( true );
}


bool AvmcodeCompiler::configureActivityPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE SELF
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( SELF  ) = NEW_COMPILER( AvmcodeSelfSuperStatementCompiler );
	OPCODE_COMPILER( SUPER ) = NEW_COMPILER( AvmcodeSelfSuperStatementCompiler );

	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE MANAGING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( CONTEXT_SWITCHER ) = NEW_COMPILER( AvmcodeContextSwitcherStatementCompiler );

	OPCODE_COMPILER( PROCESS_STATE_GET ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( PROCESS_STATE_SET ) = NEW_COMPILER( AvmcodeProcessStateSetCompiler );


	OPCODE_COMPILER( INIT    ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( FINAL   ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( DESTROY ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( START   ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( RESTART ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( STOP    ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( WAIT        ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( SUSPEND ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( RESUME  ) = ACTIVITY_STATEMENT_COMPILER;


	OPCODE_COMPILER( IENABLE_INVOKE  ) = NEW_COMPILER( AvmcodeIEnableStatementCompiler );
	OPCODE_COMPILER( ENABLE_INVOKE   ) = NEW_COMPILER( AvmcodeEnableStatementCompiler );
	OPCODE_COMPILER( ENABLE_SET      ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( IDISABLE_INVOKE ) = NEW_COMPILER( AvmcodeIDisableStatementCompiler );
	OPCODE_COMPILER( DISABLE_INVOKE  ) = NEW_COMPILER( AvmcodeDisableStatementCompiler );
	OPCODE_COMPILER( DISABLE_SET     ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( DISABLE_CHILD   ) = NOTHING_AVMCODE_COMPILER;
	OPCODE_COMPILER( DISABLE_SELF    ) = NOTHING_AVMCODE_COMPILER;
	OPCODE_COMPILER( DISABLE_SELVES  ) = NEW_COMPILER( AvmcodeDisableSelvesStatementCompiler );

	OPCODE_COMPILER( IABORT_INVOKE   ) = NEW_COMPILER( AvmcodeIAbortStatementCompiler );
	OPCODE_COMPILER( ABORT_INVOKE    ) = NEW_COMPILER( AvmcodeAbortStatementCompiler );
	OPCODE_COMPILER( ABORT_SET       ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( ABORT_CHILD     ) = NOTHING_AVMCODE_COMPILER;
	OPCODE_COMPILER( ABORT_SELF      ) = NOTHING_AVMCODE_COMPILER;
	OPCODE_COMPILER( ABORT_SELVES    ) = NEW_COMPILER( AvmcodeAbortSelvesStatementCompiler );

	OPCODE_COMPILER( HISTORY_CLEAR          ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( DEEP_HISTORY_INVOKE    ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( SHALLOW_HISTORY_INVOKE ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( IRUN ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( RUN  ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( RTC  ) = NEW_COMPILER( AvmcodeRtcStatementCompiler );


	OPCODE_COMPILER( INVOKE_NEW        ) = NEW_COMPILER( AvmcodeInvokeNewCompiler );

	OPCODE_COMPILER( INVOKE_ROUTINE    ) = NEW_COMPILER( AvmcodeInvokeRoutineCompiler );

	OPCODE_COMPILER( INVOKE_TRANSITION ) = NEW_COMPILER( AvmcodeInvokeTransitionCompiler );

	OPCODE_COMPILER( INVOKE_METHOD     ) = NEW_COMPILER( AvmcodeInvokeMethodCompiler );
	OPCODE_COMPILER( INVOKE_PROGRAM    ) = NEW_COMPILER( AvmcodeInvokeProgramCompiler );
	OPCODE_COMPILER( INVOKE_FUNCTION   ) = NEW_COMPILER( AvmcodeInvokeFunctionCompiler );


	OPCODE_COMPILER( SCHEDULE_INVOKE   ) = NEW_COMPILER( AvmcodeScheduleStatementCompiler );
	OPCODE_COMPILER( SCHEDULE_GET      ) = ACTIVITY_STATEMENT_COMPILER;
	OPCODE_COMPILER( SCHEDULE_IN       ) = NEW_COMPILER( AvmcodeScheduleInStatementCompiler );
	OPCODE_COMPILER( SCHEDULE_SET      ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( GOTO              ) = NEW_COMPILER( AvmcodeGotoStatementCompiler );

	OPCODE_COMPILER( FORK              ) = NEW_COMPILER( AvmcodeForkStatementCompiler );
	OPCODE_COMPILER( JOIN              ) = NEW_COMPILER( AvmcodeJoinStatementCompiler );

	OPCODE_COMPILER( INPUT_ENABLED     ) = NEW_COMPILER( AvmcodeInputEnabledStatementCompiler );

	OPCODE_COMPILER( RDV               ) = ACTIVITY_STATEMENT_COMPILER;

	OPCODE_COMPILER( SYNCHRONIZE       ) = ACTIVITY_STATEMENT_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureStatusPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE STATUS
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( STATUS_WAS   ) = MACHINE_STATUS_EXPRESSION_COMPILER;
	OPCODE_COMPILER( STATUS_IS    ) = MACHINE_STATUS_EXPRESSION_COMPILER;
	OPCODE_COMPILER( STATUS_BEING ) = MACHINE_STATUS_EXPRESSION_COMPILER;
	OPCODE_COMPILER( STATUS_WILL  ) = MACHINE_STATUS_EXPRESSION_COMPILER;

	OPCODE_COMPILER( CHANGED      ) = VARIABLE_STATUS_EXPRESSION_COMPILER;
	OPCODE_COMPILER( CHANGED_TO   ) = VARIABLE_STATUS_EXPRESSION_COMPILER;

	return( true );
}


bool AvmcodeCompiler::configureSchedulingPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM PROGRAM SCHEDULING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( ASYNCHRONOUS       ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( STRONG_SYNCHRONOUS ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( WEAK_SYNCHRONOUS   ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( INTERLEAVING       ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( PARTIAL_ORDER      ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( PARALLEL           ) = SCHEDULING_STATEMENT_COMPILER;

	OPCODE_COMPILER( RDV_ASYNCHRONOUS       ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( RDV_STRONG_SYNCHRONOUS ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( RDV_WEAK_SYNCHRONOUS   ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( RDV_INTERLEAVING       ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( RDV_PARTIAL_ORDER      ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( RDV_PARALLEL           ) = SCHEDULING_STATEMENT_COMPILER;


	OPCODE_COMPILER( EXCLUSIVE       ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( NONDETERMINISM  ) = SCHEDULING_STATEMENT_COMPILER;

	OPCODE_COMPILER( PRIOR_GT        ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( PRIOR_LT        ) = SCHEDULING_STATEMENT_COMPILER;

	OPCODE_COMPILER( SCHEDULE_AND_THEN ) = SCHEDULING_STATEMENT_COMPILER;
	OPCODE_COMPILER( SCHEDULE_OR_ELSE  ) = SCHEDULING_STATEMENT_COMPILER;

	OPCODE_COMPILER( ATOMIC_SEQUENCE ) = NEW_COMPILER( AvmcodeAtomicSequenceCompiler );

	OPCODE_COMPILER( SEQUENCE        ) = NEW_COMPILER( AvmcodeStrongSequenceCompiler );

	OPCODE_COMPILER( SEQUENCE_SIDE   ) = SEQUENCE_STATEMENT_COMPILER;
	OPCODE_COMPILER( SEQUENCE_WEAK   ) = SEQUENCE_STATEMENT_COMPILER;

	OPCODE_COMPILER( PRODUCT         ) = SCHEDULING_STATEMENT_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureBasicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM BUFFER MANAGING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( UPDATE_BUFFER  ) = DEFAULT_AVMCODE_COMPILER;


	////////////////////////////////////////////////////////////////////////////
	// AVM PRIMITIVE STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( ASSIGN       ) = NEW_COMPILER( AvmcodeAssignCompiler );
	OPCODE_COMPILER( ASSIGN_AFTER ) = NEW_COMPILER( AvmcodeAssignAfterCompiler );

	OPCODE_COMPILER( ASSIGN_OP       ) = NEW_COMPILER( AvmcodeAssignOpCompiler );
	OPCODE_COMPILER( ASSIGN_OP_AFTER ) = NEW_COMPILER( AvmcodeAssignOpAfterCompiler );

	OPCODE_COMPILER( ASSIGN_REF   ) = NEW_COMPILER( AvmcodeAssignRefCompiler );
	OPCODE_COMPILER( ASSIGN_MACRO ) = NEW_COMPILER( AvmcodeAssignMacroCompiler );

	OPCODE_COMPILER( ASSIGN_NEWFRESH ) = NEW_COMPILER( AvmcodeAssignUnaryCompiler );
	OPCODE_COMPILER( ASSIGN_RESET    ) = OPCODE_COMPILER( ASSIGN_NEWFRESH );

	OPCODE_COMPILER( GUARD       ) = NEW_COMPILER( AvmcodeGuardCompiler );
	OPCODE_COMPILER( TIMED_GUARD ) = NEW_COMPILER( AvmcodeTimedGuardCompiler );
	OPCODE_COMPILER( EVENT       ) = NEW_COMPILER( AvmcodeEventCompiler );
	OPCODE_COMPILER( CHECK_SAT   ) = NEW_COMPILER( AvmcodeChecksatCompiler );

	OPCODE_COMPILER( INPUT       ) = NEW_COMPILER( AvmcodeInputCompiler );
	OPCODE_COMPILER( INPUT_FROM  ) = NEW_COMPILER( AvmcodeInputFromCompiler );
	OPCODE_COMPILER( INPUT_SAVE  ) = NEW_COMPILER( AvmcodeInputSaveCompiler );

	OPCODE_COMPILER( INPUT_VAR   ) = NEW_COMPILER( AvmcodeInputVarCompiler );
	OPCODE_COMPILER( INPUT_ENV   ) = NEW_COMPILER( AvmcodeInputEnvCompiler );

	OPCODE_COMPILER( OUTPUT      ) = NEW_COMPILER( AvmcodeOutputCompiler );
	OPCODE_COMPILER( OUTPUT_TO   ) = NEW_COMPILER( AvmcodeOutputToCompiler );
	OPCODE_COMPILER( OUTPUT_VAR  ) = NEW_COMPILER( AvmcodeOutputVarCompiler );
	OPCODE_COMPILER( OUTPUT_ENV ) = NEW_COMPILER( AvmcodeOutputEnvCompiler );

	OPCODE_COMPILER( PRESENT     ) = NEW_COMPILER( AvmcodeAbsentPresentCompiler );
	OPCODE_COMPILER( ABSENT      ) = OPCODE_COMPILER( PRESENT );

	OPCODE_COMPILER( IF          ) = ITE_STATEMENT_COMPILER;
	OPCODE_COMPILER( IFE         ) = ITE_STATEMENT_COMPILER;

	OPCODE_COMPILER( FOR         ) = NEW_COMPILER( AvmcodeForCompiler );
	OPCODE_COMPILER( FOREACH     ) = NEW_COMPILER( AvmcodeForeachCompiler );
	OPCODE_COMPILER( WHILE_DO    ) = NEW_COMPILER( AvmcodeWhileDoCompiler );
	OPCODE_COMPILER( DO_WHILE    ) = NEW_COMPILER( AvmcodeDoWhileCompiler );

	OPCODE_COMPILER( BREAK       ) = NEW_COMPILER( AvmcodeBreakCompiler );
	OPCODE_COMPILER( CONTINUE    ) = NEW_COMPILER( AvmcodeContinueCompiler );
	OPCODE_COMPILER( RETURN      ) = NEW_COMPILER( AvmcodeReturnCompiler );
	OPCODE_COMPILER( EXIT        ) = NEW_COMPILER( AvmcodeExitCompiler );

	OPCODE_COMPILER( STEP_MARK   ) = DEFAULT_AVMCODE_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureBitwisePrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM BITWISE EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPILER( BNOT   ) = UNARY_BITWISE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( BAND   ) = ASSOCIATIVE_BITWISE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( BOR    ) = ASSOCIATIVE_BITWISE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( BXOR   ) = BINARY_BITWISE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( LSHIFT ) = BINARY_BITWISE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( RSHIFT ) = BINARY_BITWISE_EXPRESSION_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureLogicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM PREDICAT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPILER( NOT  ) = UNARY_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( AND  ) = ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( NAND ) = ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( XAND ) = BINARY_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( OR   ) = ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( NOR  ) = ASSOCIATIVE_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( XOR  ) = BINARY_PREDICATE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( XNOR ) = BINARY_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( IMPLIES ) = BINARY_PREDICATE_EXPRESSION_COMPILER;

	OPCODE_COMPILER( EXISTS ) = QUANTIFIED_PREDICATE_EXPRESSION_COMPILER;
	OPCODE_COMPILER( FORALL ) = QUANTIFIED_PREDICATE_EXPRESSION_COMPILER;


	////////////////////////////////////////////////////////////////////////////
	// AVM COMPARISON EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPILER( EQ   ) = RELATIONAL_EXPRESSION_COMPILER;
	OPCODE_COMPILER( NEQ  ) = RELATIONAL_EXPRESSION_COMPILER;

	OPCODE_COMPILER( SEQ  ) = RELATIONAL_EXPRESSION_COMPILER;
	OPCODE_COMPILER( NSEQ ) = RELATIONAL_EXPRESSION_COMPILER;

	OPCODE_COMPILER( LT   ) = RELATIONAL_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LTE  ) = RELATIONAL_EXPRESSION_COMPILER;

	OPCODE_COMPILER( GT   ) = RELATIONAL_EXPRESSION_COMPILER;
	OPCODE_COMPILER( GTE  ) = RELATIONAL_EXPRESSION_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureArithmeticPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM ARITHMETIC EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPILER( PLUS   ) = ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER;
	OPCODE_COMPILER( MINUS  ) = ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER;
	OPCODE_COMPILER( UMINUS ) = UNARY_ARITHMETIC_EXPRESSION_COMPILER;

	OPCODE_COMPILER( MULT   ) = ASSOCIATIVE_ARITHMETIC_EXPRESSION_COMPILER;
	OPCODE_COMPILER( POW    ) = BINARY_ARITHMETIC_EXPRESSION_COMPILER;

	OPCODE_COMPILER( DIV    ) = BINARY_ARITHMETIC_EXPRESSION_COMPILER;
	OPCODE_COMPILER( MOD    ) = BINARY_ARITHMETIC_EXPRESSION_COMPILER;


	return( true );
}


bool AvmcodeCompiler::configureLookupPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// LOOKUP STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( LOOKUP_INT       ) = LOOKUP_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LOOKUP_INT_EXT   ) = LOOKUP_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LOOKUP_NEAREST   ) = LOOKUP_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LOOKUP_BELOW     ) = LOOKUP_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LOOKUP_ABOVE     ) = LOOKUP_EXPRESSION_COMPILER;
	OPCODE_COMPILER( LOOKUP2D_INT_EXT ) = LOOKUP_EXPRESSION_COMPILER;

	return( true );
}


bool AvmcodeCompiler::configureMathematicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MATHEMATICAL FUNCTION
	////////////////////////////////////////////////////////////////////////////

	// MIN - MAX
	OPCODE_COMPILER( MIN ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( MAX ) = MATH_FUNCTION_COMPILER;

	// RANDOM
	OPCODE_COMPILER( RANDOM ) = MATH_FUNCTION_COMPILER;

	// ABS
	OPCODE_COMPILER( ABS ) = MATH_FUNCTION_COMPILER;

	// ROUNDING
	OPCODE_COMPILER( CEIL     ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( FLOOR    ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ROUND    ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( TRUNCATE ) = MATH_FUNCTION_COMPILER;


	// EXP - LOG
	OPCODE_COMPILER( SQRT ) = MATH_FUNCTION_COMPILER;

	OPCODE_COMPILER( EXP  ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( LOG  ) = MATH_FUNCTION_COMPILER;

	// TRIGONOMETRIC
	OPCODE_COMPILER( SIN ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( COS ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( TAN ) = MATH_FUNCTION_COMPILER;

	OPCODE_COMPILER( SINH ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( COSH ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( TANH ) = MATH_FUNCTION_COMPILER;

	OPCODE_COMPILER( ASIN  ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ACOS  ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ATAN  ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ATAN2 ) = MATH_FUNCTION_COMPILER;

	OPCODE_COMPILER( ASINH ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ACOSH ) = MATH_FUNCTION_COMPILER;
	OPCODE_COMPILER( ATANH ) = MATH_FUNCTION_COMPILER;

	return( true );
}


bool AvmcodeCompiler::configureStringCollectionPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM STRING / COLLECTION OPERATOR
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPILER( CONTAINS    ) = BINARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( IN          ) = BINARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( NOTIN       ) = BINARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( SUBSET      ) = BINARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( SUBSETEQ    ) = BINARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( INTERSECT   ) = BINARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( STARTS_WITH ) = BINARY_STRING_EXPRESSION_COMPILER;
	OPCODE_COMPILER( ENDS_WITH   ) = BINARY_STRING_EXPRESSION_COMPILER;
	OPCODE_COMPILER( CONCAT      ) = ASSOCIATIVE_STRING_EXPRESSION_COMPILER;

	OPCODE_COMPILER( PUSH        ) = NEW_COMPILER( AvmcodePushCompiler );
	OPCODE_COMPILER( ASSIGN_TOP  ) = NEW_COMPILER( AvmcodeAssignTopCompiler );
	OPCODE_COMPILER( TOP         ) = NEW_COMPILER( AvmcodeTopCompiler );
	OPCODE_COMPILER( POP         ) = NEW_COMPILER( AvmcodePopCompiler );
	OPCODE_COMPILER( POP_FROM    ) = NEW_COMPILER( AvmcodePopFromCompiler );

	OPCODE_COMPILER( EMPTY       ) = UNARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( NONEMPTY    ) = UNARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( SINGLETON   ) = UNARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( POPULATED   ) = UNARY_CONTAINER_STATEMENT;
	OPCODE_COMPILER( FULL        ) = UNARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( SIZE        ) = UNARY_CONTAINER_STATEMENT;

	OPCODE_COMPILER( APPEND      ) = BINARY_WRITE_CONTAINER_STATEMENT;

	OPCODE_COMPILER( REMOVE      ) = BINARY_WRITE_CONTAINER_STATEMENT;

	OPCODE_COMPILER( CLEAR       ) = UNARY_WRITE_CONTAINER_STATEMENT;

	OPCODE_COMPILER( RESIZE      ) = BINARY_WRITE_CONTAINER_STATEMENT;

	return( true );
}


bool AvmcodeCompiler::configureIoltPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// IOLTL BEHAVIORAL PREDICAT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( GLOBALLY   ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( UNTIL      ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( NEXT       ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( EVENTUALLY ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( RELEASES   ) = DEFAULT_AVMCODE_COMPILER;

	OPCODE_COMPILER( OBS        ) = NEW_COMPILER( AvmcodeObsCompiler );


	////////////////////////////////////////////////////////////////////////////
	// IOLTL LOGICAL PREDICAT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPILER( AND_T ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( OR_T  ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( NOT_T ) = DEFAULT_AVMCODE_COMPILER;
	OPCODE_COMPILER( IMP_T ) = DEFAULT_AVMCODE_COMPILER;


	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the COMPILER of ARGUMENT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

const BF & AvmcodeCompiler::postCompileSymbol(const BF & aSymbol)
{
	if( aSymbol.is< InstanceOfData >() )
	{
		const InstanceOfData & anInstance = aSymbol.to< InstanceOfData >();

		if( anInstance.getModifier().hasFeatureFinal()
			&& anInstance.hasValue() )
		{
			if( anInstance.isTypedEnum() )
			{
				return( aSymbol );
			}
			else if( anInstance.getModifier().hasNatureParameter()
					|| anInstance.hasArrayIndexPointer() )
			{
				return( aSymbol );
			}
			else
			{
				return( anInstance.getValue() );
			}
		}
		else
		{
			return( aSymbol );
		}
	}

	else if( aSymbol.is< InstanceOfMachine >() )
	{
		if( aSymbol.to< InstanceOfMachine >().hasRuntimeRID() )
		{
			return( aSymbol.to< InstanceOfMachine >().getRuntimeRID() );
		}
		return( aSymbol );
	}

	else //if( aSymbol.is< UniFormIdentifier >() || aSymbol.is< AvmCode >() )
	{
		return( aSymbol );
	}
}


BF AvmcodeCompiler::compileUFI(
		COMPILE_CONTEXT * aCTX, const UniFormIdentifier & anUFI)
{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<UFI>: "
			<< anUFI.str() << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	BF aSymbol = UFI_EXPRESSION_COMPILER->compileUfiExpression(aCTX, anUFI);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
		AVM_OS_TRACE << TAB_DECR_INDENT << ">| result"
				<< ((aSymbol.is< UniFormIdentifier >()) ? "<UFI>: " : ":> ")
				<< str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( postCompileSymbol(aSymbol) );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << anUFI.errorLocation(aCTX->mCompileCtx->safeAstElement())
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( BF::REF_NULL );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << anUFI.errorLocation(aCTX->mCompileCtx->safeAstElement())
				<< "UFI compilation error : unfound symbol << "
				<< anUFI.str() << " >>" << std::endl << std::endl;

		return( BF::REF_NULL );
	}
}


BF AvmcodeCompiler::compileFullyQualifiedNameID(
		COMPILE_CONTEXT * aCTX, const std::string & aFullyQualifiedNameID)
{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<fqn>: "
			<< aFullyQualifiedNameID << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	BF aSymbol = getSymbolTable().searchSymbol(aCTX, aFullyQualifiedNameID);

	if( aSymbol.invalid() )
	{
		UniFormIdentifier anFQN(aFullyQualifiedNameID);

		aSymbol = getSymbolTable().searchSymbolByFQN(aCTX, anFQN);
//		aSymbol = UFI_EXPRESSION_COMPILER->compileUfiExpression(aCTX, anFQN);
	}

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result"
			<< ((aSymbol.is< UniFormIdentifier >())? "<fqn>: " : ":> ")
			<< str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( postCompileSymbol(aSymbol) );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( ExpressionConstructor::
				newQualifiedIdentifier(aFullyQualifiedNameID) );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "FullyQualifiedNameID compilation error : unfound symbol << "
				<< aFullyQualifiedNameID << " >>"
				<< std::endl << std::endl;

		return( ExpressionConstructor::
				newQualifiedIdentifier(aFullyQualifiedNameID) );
	}
}


BF AvmcodeCompiler::compileQualifiedIdentifier(
		COMPILE_CONTEXT * aCTX, const BF & aQualifiedNameID)
{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<QualifiedNameID>: "
			<< aQualifiedNameID.str() << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().
			searchSymbolByQualifiedNameID(aCTX, aQualifiedNameID.str());

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result :> "
			<< str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( postCompileSymbol(aSymbol) );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aQualifiedNameID );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "[ [ Fully ] Qualified ] Name ID compilation error : "
					"unfound symbol << " << aQualifiedNameID.str() << " >>"
				<< std::endl << std::endl;

		return( aQualifiedNameID );
	}
}


BF AvmcodeCompiler::compileQualifiedPositionalIdentifier(
		COMPILE_CONTEXT * aCTX, const BF & aQualifiedNameID)
{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "<| compiling<QualifiedPositionalIdentifier>: "
			<< aQualifiedNameID.str() << std::endl
			<< TAB2 << str_header( aCTX ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().
			searchSymbolByQualifiedNameID(aCTX, aQualifiedNameID.str());

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result"
			<< ((aSymbol.is< UniFormIdentifier >())? "<qnid>: " : ":> ")
			<< str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		if( aSymbol.is< InstanceOfMachine >() )
		{
			ExecutableForm * anExecutable =
					aSymbol.to< InstanceOfMachine >().getExecutable();
			if( anExecutable != nullptr )
			{
				avm_offset_t aPositionOffset = aQualifiedNameID.
						to< QualifiedIdentifier >().getPositionOffset();

				if( aPositionOffset < anExecutable->getParamCount() )
				{
					return( anExecutable->getParam(aPositionOffset) );
				}
			}
			return( aSymbol );
		}

		return( postCompileSymbol(aSymbol) );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aQualifiedNameID );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "[ [ Fully ] Qualified ] Name ID compilation error :"
					" unfound symbol << " << aQualifiedNameID.str() << " >>"
				<< std::endl << std::endl;

		return( aQualifiedNameID );
	}
}


BF AvmcodeCompiler::compileIdentifier(
		COMPILE_CONTEXT * aCTX, const std::string & aNameID)
{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<name-id>: "
			<< aNameID << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchSymbolByNameID(aCTX, aNameID);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result"
			<< ((aSymbol.is< UniFormIdentifier >())? "<name-id>: " : ":> ")
			<< str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( postCompileSymbol(aSymbol) );
	}

	else
	{
		const InstanceOfData * varCtx = aCTX->mVariableCtx;
		for( ; varCtx != nullptr ; varCtx = varCtx->getParent() )
		{
			BF aFieldSymbol = getSymbolTable().searchSymbol(aCTX,
					( OSS() << varCtx->getFullyQualifiedNameID()
							<< '.' << aNameID ) );

			if( aFieldSymbol.valid() )
			{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
			<< str_header( aFieldSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

				return( postCompileSymbol(aFieldSymbol) );
			}
		}

		const Operator * opID = OperatorManager::getOp( aNameID );

		if( opID != nullptr )
		{
			return( CONST_BF_OP( opID ) );
		}
		// ERROR REPORTING
		else if( getSymbolTable().hasError() )
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< getSymbolTable().getErrorMessage()
					<< std::endl << std::endl;

			return( ExpressionConstructor::newIdentifier(aNameID) );
		}
		else
		{
			getCompilerTable().incrErrorCount();
			aCTX->errorContext( AVM_OS_WARN )
					<< "Identifier compilation error : unfound symbol << "
					<< aNameID << " >>" << std::endl << std::endl;

			return( ExpressionConstructor::newIdentifier(aNameID) );
		}
	}
}


const BF & AvmcodeCompiler::compileElement(
		COMPILE_CONTEXT * aCTX, const BF & anElement)
{
	const ObjectElement & astElement = anElement.to< ObjectElement >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<FORM>: & "
			<< astElement.getFullyQualifiedNameID() << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchSymbol(aCTX, astElement);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| result:> " << str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( postCompileSymbol(aSymbol) );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astElement.errorLocation(
					aCTX->mCompileCtx->safeAstElement())
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( anElement );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound data instance << & "
				<< astElement.getFullyQualifiedNameID() << " >>"
				<< std::endl << std::endl;

		return( anElement );
	}
}


const BF & AvmcodeCompiler::compileDataType(
		COMPILE_CONTEXT * aCTX, const BF & aDataType)
{
	const DataType & astType = aDataType.to< DataType >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<DataType>: "
			<< str_header( astType ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const TypeSpecifier & aTypeSpecifier =
			SymbolTable::searchTypeSpecifier(
					getConfiguration().getExecutableSystem(), aCTX, astType);

	if( aTypeSpecifier.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
			<< str_header( aTypeSpecifier ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aTypeSpecifier );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astType.errorLocation(aCTX->mCompileCtx->safeAstElement())
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aDataType );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound typedef << & " << str_header( astType )
				<< " >>" << std::endl << std::endl;

		return( aDataType );
	}
}


const BF & AvmcodeCompiler::compileVariable(
		COMPILE_CONTEXT * aCTX, const BF & aVariable)
{
	const Variable & astVariable = aVariable.to< Variable >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Variable>: "
			<< str_header( astVariable ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchDataInstance(aCTX, astVariable);

	if( aSymbol.valid() )
	{
		const InstanceOfData & anInstance = aSymbol.to< InstanceOfData >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| result:> " << str_header( anInstance ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		if( anInstance.getModifier().hasFeatureFinal() )
		{
			if( (not anInstance.hasValue()) && astVariable.hasValue() )
			{
				const_cast< InstanceOfData & >(anInstance).setValue(
						decode_compileExpression(
								aCTX->clone(anInstance.getTypeSpecifier()),
								astVariable.getValue() ) );
			}

			if( anInstance.hasValue() )
			{
				if( anInstance.isEnumSymbolPointer()
					&& anInstance.getModifier().hasFeatureUnsafe() )
				{
					return( aSymbol );
				}
				else if( anInstance.getModifier().hasNatureParameter()
						|| anInstance.hasArrayIndexPointer() )
				{
					return( aSymbol );
				}
				else
				{
					return( anInstance.getValue() );
				}
			}
		}

		return( aSymbol );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astVariable.errorLocation(
				aCTX->mCompileCtx->safeAstElement() )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;


AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| error:> " << str_header( astVariable ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aVariable );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound variable instance << "
				<< astVariable.getFullyQualifiedNameID() << " >>"
				<< std::endl << std::endl;

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| error:> " << str_header( astVariable ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aVariable );
	}
}


const BF & AvmcodeCompiler::compileBuffer(
		COMPILE_CONTEXT * aCTX, const BF & aBuffer)
{
	const Buffer & astBuffer = aBuffer.to< Buffer >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Buffer>: "
			<< str_header( astBuffer ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchBufferInstance(
			aCTX->mCompileCtx->getExecutable(), astBuffer);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
			<< str_header( aSymbol.to_ptr< InstanceOfBuffer >() ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aSymbol );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astBuffer.errorLocation(aCTX->mCompileCtx->safeAstElement())
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aBuffer );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound buffer instance << & " << str_header( astBuffer )
				<< " >>" << std::endl << std::endl;

		return( aBuffer );
	}
}


const BF & AvmcodeCompiler::compilePort(
		COMPILE_CONTEXT * aCTX, const BF & aPort)
{
	const Port & astPort = aPort.to< Port >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Port>: "
			<< str_header( astPort ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchPortSymbolInstance(
			aCTX->mCompileCtx->getExecutable(), astPort);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
			<< str_header( aSymbol.to< InstanceOfPort >() ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aSymbol );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astPort.errorLocation(aCTX->mCompileCtx->safeAstElement())
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aPort );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound port instance << " << str_header( astPort ) << " >>"
				<< std::endl << std::endl;

		return( aPort );
	}
}


const BF & AvmcodeCompiler::compileConnector(
		COMPILE_CONTEXT * aCTX, const BF & aConnector)
{
	return( aConnector );
}


const BF & AvmcodeCompiler::compileMachine(
		COMPILE_CONTEXT * aCTX, const BF & aMachine)
{
	const Machine & astMachine = aMachine.to< Machine >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Machine>: "
			<< str_header( astMachine ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol =
			getSymbolTable().searchInstanceStatic(aCTX, astMachine);

	if( aSymbol.valid() )
	{
		InstanceOfMachine * aMachineSymbol =
				aSymbol.to_ptr< InstanceOfMachine >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
			<< str_header( aMachineSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		if( aMachineSymbol->hasRuntimeRID() )
		{
			AVM_OS_TRACE << TAB_DECR_INDENT << ">| result:> "
					<< aMachineSymbol->getRuntimeRID().str() << std::endl;

			return( aMachineSymbol->getRuntimeRID() );
		}

		return( aSymbol );
	}

	const BF & aSymbolModel =
			getSymbolTable().searchInstanceModel(aCTX, astMachine);

	if( aSymbolModel.valid() )
	{
		return( aSymbolModel );
	}

	if( astMachine.getSpecifier().isDesignInstanceDynamic() )
	{
		const BF & aSymbol =
				getSymbolTable().searchInstanceDynamic(aCTX, astMachine);

		if( aSymbol.valid() )
		{
			return( aSymbol );
		}
	}

	// ERROR REPORTING
	if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astMachine.errorLocation(
				aCTX->mCompileCtx->safeAstElement() )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aMachine );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound machine << " << str_header( astMachine )
				<< " >>" << std::endl << std::endl;

		return( aMachine );
	}
}


const BF & AvmcodeCompiler::compileRoutine(
		COMPILE_CONTEXT * aCTX, const BF & aRoutine)
{
	const Routine & astRoutine = aRoutine.to< Routine >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Routine>: "
			<< str_header( astRoutine ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol =
			getSymbolTable().searchProgram(aCTX, astRoutine.getNameID());

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| result:> " << str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aSymbol );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astRoutine.errorLocation(
				aCTX->mCompileCtx->safeAstElement() )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aRoutine );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound routine << & " << str_header( astRoutine )
				<< " >>" << std::endl << std::endl;

		return( aRoutine );
	}
}


const BF & AvmcodeCompiler::compileTransition(
		COMPILE_CONTEXT * aCTX, const BF & aTransition)
{
	const Transition & astTransition = aTransition.to< Transition >();

AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<| compiling<Transition>: "
			<< str_header( astTransition ) << std::endl;
	aCTX->debugContext( AVM_OS_TRACE << INCR_INDENT ) << DECR_INDENT;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

	const BF & aSymbol = getSymbolTable().searchTransition(aCTX, astTransition);

	if( aSymbol.valid() )
	{
AVM_IF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< ">| result:> " << str_header( aSymbol ) << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , QUALIFIED_NAME_ID )

		return( aSymbol );
	}

	// ERROR REPORTING
	else if( getSymbolTable().hasError() )
	{
		getCompilerTable().incrErrorCount();
		AVM_OS_WARN << astTransition.errorLocation(
				aCTX->mCompileCtx->safeAstElement() )
				<< getSymbolTable().getErrorMessage()
				<< std::endl << std::endl;

		return( aTransition );
	}
	else
	{
		getCompilerTable().incrErrorCount();
		aCTX->errorContext( AVM_OS_WARN )
				<< "Unfound transition << & " << str_header( astTransition )
				<< " >>" << std::endl << std::endl;

		return( aTransition );
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the COMPILER of EXPRESSION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeCompiler::compileExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "in<expr>: "
			<< STRIML( aCode->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )


	BF expr = AVMCODE_COMPILER_TABLE[ aCode->getOpOffset() ]->
			compileExpression(aCTX, aCode);


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "out:> "
			<< STRIML( expr.toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	return( expr );
}


BF AvmcodeCompiler::decode_compileExpression(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( compileExpression(aCTX, aCode.bfCode()) );
		}

		case FORM_UFI_KIND:
		{
			return( compileUFI(aCTX, aCode.to< UniFormIdentifier>()) );
		}

		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			if( aCode.str().find(':') != std::string::npos )
			{
				return( compileFullyQualifiedNameID(aCTX, aCode) );
			}
			else
			{
				return( compileQualifiedIdentifier(aCTX, aCode) );
			}
		}
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( compileIdentifier(aCTX, aCode) );
		}

		case FORM_XFSP_VARIABLE_KIND:
		{
			return( compileVariable(aCTX, aCode) );
		}

		case FORM_XFSP_DATATYPE_KIND:
		{
			return( compileDataType(aCTX, aCode) );
		}

		case FORM_TYPE_SPECIFIER_KIND:
		{
			return( aCode );
		}

		case FORM_XFSP_MACHINE_KIND:
		case FORM_XFSP_SYSTEM_KIND:
		{
			return( compileMachine(aCTX, aCode) );
		}

//		case FORM_XFSP_INSTANCE_KIND:
//		{
//			return( compileInstance(aCTX, aCode) );
//		}

		case FORM_XFSP_BUFFER_KIND:
		{
			return( compileBuffer(aCTX, aCode) );
		}

		case FORM_XFSP_PORT_KIND:
		{
			return( compilePort(aCTX, aCode) );
		}

		case FORM_XFSP_TRANSITION_KIND:
		{
			return( compileTransition(aCTX, aCode) );
		}

		case FORM_XFSP_ROUTINE_KIND:
		{
			return( compileRoutine(aCTX, aCode) );
		}


		case FORM_XFSP_PACKAGE_KIND:
		case FORM_XFSP_CHANNEL_KIND:
		case FORM_XFSP_COM_POINT_KIND:
		case FORM_XFSP_COM_ROUTE_KIND:
		case FORM_XFSP_CONNECTOR_KIND:

		case FORM_OPERATOR_KIND:

		case FORM_EXECUTABLE_MACHINE_KIND:

		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_DATA_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		case FORM_BUILTIN_STRING_KIND:
		{
			return( aCode );
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		{
			const BuiltinArray & aBuiltinArray = aCode.to< BuiltinArray >();

			// Build the type specified container
			if( (aCTX->mType != nullptr)
				&& aCTX->mType->hasTypeCollection()
				&& aCTX->mType->is< ContainerTypeSpecifier >() )
			{
				BuiltinContainer * containerValue = BuiltinContainer::create(
						aCTX->mType->to< ContainerTypeSpecifier >() );

				containerValue->copy( aBuiltinArray, std::min(
						containerValue->capacity(), aBuiltinArray.size()) );

				return( BF( containerValue ) );
			}
			else
			{
				return( BF( aBuiltinArray.getArrayBF() ) );
			}
		}

		case FORM_ARRAY_IDENTIFIER_KIND:
		{
			return( compileArrayOfIdentifier(aCTX,
					aCode.to_ptr< ArrayIdentifier >()) );
		}

		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			return( compileArrayOfQualifiedIdentifier(aCTX,
					aCode.to_ptr< ArrayQualifiedIdentifier >()) );
		}

		case FORM_ARRAY_BF_KIND:
		{
			return( compileArrayOfBF(aCTX, aCode.to_ptr< ArrayBF >()) );
		}

		case FORM_CONTAINER_VECTOR_KIND:
		case FORM_CONTAINER_REVERSE_VECTOR_KIND:
		case FORM_CONTAINER_LIST_KIND:
		case FORM_CONTAINER_SET_KIND:
		case FORM_CONTAINER_BAG_KIND:
		case FORM_CONTAINER_FIFO_KIND:
		case FORM_CONTAINER_LIFO_KIND:
		{
			return( aCode );
		}

		default:
		{ // TODO
			AVM_OS_WARNING_ALERT
					<< "AvmcodeCompiler is trying to decode_compileExpression"
					"\n\ttypeinfo: " << aCode.raw_pointer()->classKindInfo()
					<< "\n\t<< " << aCode.str() << " >> !!!"
					<< SEND_ALERT;

			return( BF::REF_NULL );
		}
	}

	return( aCode );
}



BF AvmcodeCompiler::compileArrayOfIdentifier(
		COMPILE_CONTEXT * aCTX, ArrayIdentifier * idArray)
{
	const BaseTypeSpecifier & arrayType = ( (aCTX->mType != nullptr)
			&& aCTX->mType->hasTypeComposite()) ? (* aCTX->mType) :
					idArray->getTypeSpecifier();

	ArrayBF * compiledArray = new ArrayBF(arrayType, idArray->size());

	compiledArray->setTypeSpecifier( arrayType );

	bool isnotCompiled = false;

	if( aCTX->mType != nullptr )
	{
		COMPILE_CONTEXT * contentCTX = nullptr;

		if( aCTX->mType->hasTypeCollection()
			&& aCTX->mType->is< ContainerTypeSpecifier >() )
		{
			contentCTX = aCTX->clone( aCTX->mType->
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier() );

			for( std::size_t index = 0; index < idArray->size() ; ++index )
			{
				compiledArray->set( index,
						compileIdentifier(contentCTX, idArray->get(index)) );
			}
		}
		else if( aCTX->mType->isTypedStructure() )
		{
			const ClassTypeSpecifier * typeStruct =
					aCTX->mType->to_ptr< ClassTypeSpecifier >();
			TableOfSymbol::const_iterator itField =
					typeStruct->getSymbolData().begin();
			TableOfSymbol::const_iterator endField =
					typeStruct->getSymbolData().end();

			for( std::size_t index = 0; (index < idArray->size())
					&& (itField != endField) ; ++index, ++itField )
			{
				contentCTX = aCTX->clone( (*itField).getTypeSpecifier() );

				compiledArray->set( index,
						compileIdentifier(contentCTX, idArray->get(index)) );
			}
		}
		else
		{
			isnotCompiled = true;
		}
	}

	if( isnotCompiled )
	{
		for( std::size_t index = 0; index < idArray->size() ; ++index )
		{
			compiledArray->set( index,
					compileIdentifier(aCTX, idArray->get(index)) );
		}
	}

	// Build the type specified container
	if( (aCTX->mType != nullptr) && aCTX->mType->hasTypeCollection()
		&& aCTX->mType->is< ContainerTypeSpecifier >() )
	{
		BuiltinContainer * containerValue = BuiltinContainer::create(
				aCTX->mType->to< ContainerTypeSpecifier >() );

		containerValue->copy( (* compiledArray), std::min(
				containerValue->capacity(), compiledArray->size()) );

		return( BF( containerValue ) );
	}
	else
	{
		return( BF( compiledArray ) );
	}
}


BF AvmcodeCompiler::compileArrayOfQualifiedIdentifier(
		COMPILE_CONTEXT * aCTX, ArrayQualifiedIdentifier * ufidArray)
{
	const BaseTypeSpecifier & arrayType = ( (aCTX->mType != nullptr)
			&& aCTX->mType->hasTypeComposite()) ? (* aCTX->mType) :
					ufidArray->getTypeSpecifier();

	ArrayBF * compiledArray = new ArrayBF(arrayType, ufidArray->size());

	compiledArray->setTypeSpecifier( arrayType );

	bool isnotCompiled = false;

	if( aCTX->mType != nullptr )
	{
		COMPILE_CONTEXT * contentCTX = nullptr;

		if( aCTX->mType->hasTypeCollection()
			&& aCTX->mType->is< ContainerTypeSpecifier >() )
		{
			contentCTX = aCTX->clone( aCTX->mType->
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier() );

			for( std::size_t index = 0; index < ufidArray->size() ; ++index )
			{
				compiledArray->set( index,
						compileFullyQualifiedNameID(
								contentCTX, ufidArray->get(index)) );
			}
		}
		else if( aCTX->mType->isTypedStructure() )
		{
			const ClassTypeSpecifier * typeStruct =
					aCTX->mType->to_ptr< ClassTypeSpecifier >();
			TableOfSymbol::const_iterator itField =
					typeStruct->getSymbolData().begin();
			TableOfSymbol::const_iterator endField =
					typeStruct->getSymbolData().end();

			for( std::size_t index = 0; (index < ufidArray->size())
					&& (itField != endField) ; ++index , ++itField )
			{
				contentCTX = aCTX->clone(
						(*itField).getTypeSpecifier() );

				compiledArray->set( index,
						compileFullyQualifiedNameID(
								contentCTX, ufidArray->get(index)) );
			}
		}
		else
		{
			isnotCompiled = true;
		}
	}

	if( isnotCompiled )
	{
		for( std::size_t index = 0; index < ufidArray->size() ; ++index )
		{
			compiledArray->set( index,
					compileFullyQualifiedNameID(aCTX, ufidArray->get(index)) );
		}
	}

	// Build the type specified container
	if( (aCTX->mType != nullptr) && aCTX->mType->hasTypeCollection()
		&& aCTX->mType->is< ContainerTypeSpecifier >() )
	{
		BuiltinContainer * containerValue = BuiltinContainer::create(
				aCTX->mType->to< ContainerTypeSpecifier >() );

		containerValue->copy( (* compiledArray), std::min(
				containerValue->capacity(), compiledArray->size()) );

		return( BF( containerValue ) );
	}
	else
	{
		return( BF( compiledArray ) );
	}
}


BF AvmcodeCompiler::compileArrayOfBF(
		COMPILE_CONTEXT * aCTX, ArrayBF * bfarray)
{
	const BaseTypeSpecifier & arrayType =
			( (aCTX->mType != nullptr) && aCTX->mType->hasTypeComposite() ) ?
					(* aCTX->mType) : bfarray->getTypeSpecifier();

	ArrayBF * compiledArray = new ArrayBF(arrayType, bfarray->size());

	compiledArray->setTypeSpecifier( arrayType );

	BF bfCompiledArray( compiledArray );

	bool isnotCompiled = false;

	if( aCTX->mType != nullptr )
	{
		COMPILE_CONTEXT * contentCTX = nullptr;

		if( aCTX->mType->hasTypeCollection()
			&& aCTX->mType->is< ContainerTypeSpecifier >() )
		{
			contentCTX = aCTX->clone( aCTX->mType->
					to< ContainerTypeSpecifier >().getContentsTypeSpecifier() );

			for( std::size_t index = 0; index < bfarray->size() ; ++index )
			{
				compiledArray->set( index , decode_compileExpression(
						contentCTX, bfarray->at(index) ) );
			}
		}
		else if( aCTX->mType->isTypedStructure() )
		{
			const ClassTypeSpecifier * typeStruct =
					aCTX->mType->to_ptr< ClassTypeSpecifier >();
			TableOfSymbol::const_iterator itField =
					typeStruct->getSymbolData().begin();
			TableOfSymbol::const_iterator endField =
					typeStruct->getSymbolData().end();

			for( std::size_t index = 0; (index < bfarray->size())
					&& (itField != endField) ; ++index , ++itField )
			{
				contentCTX = aCTX->clone(
						(*itField).getTypeSpecifier() );

				compiledArray->set( index , decode_compileExpression(
						contentCTX, bfarray->at(index) ) );
			}
		}
		else
		{
			isnotCompiled = true;
		}
	}

	if( isnotCompiled )
	{
		for( std::size_t index = 0; index < bfarray->size() ; ++index )
		{
			compiledArray->set( index ,
					decode_compileExpression(
							aCTX, bfarray->at(index) ) );
		}
	}

	// Build the type specified container
	if( (aCTX->mType != nullptr) && aCTX->mType->hasTypeCollection()
		&& aCTX->mType->is< ContainerTypeSpecifier >() )
	{
		if( AbstractAvmcodeCompiler::
				mustBeEvaluatedArgumentArray( compiledArray ) )
		{
			return( ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_CTOR,
					INCR_BF( const_cast< BaseTypeSpecifier * >(aCTX->mType) ),
					bfCompiledArray) );
		}
		else
		{
			BuiltinContainer * containerValue = BuiltinContainer::create(
					aCTX->mType->as< ContainerTypeSpecifier >() );

			containerValue->copy( (* compiledArray), std::min(
					containerValue->capacity(), compiledArray->size()) );

			return( BF( containerValue ) );
		}
	}
	else
	{
		return( bfCompiledArray );
	}
}




BF AvmcodeCompiler::decode_compileVariableMachine(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	BF varCode = decode_compileExpression(aCTX, aCode);
	if( varCode.is< InstanceOfMachine >() )
	{
		if( varCode.to< InstanceOfMachine >().hasRuntimeRID() )
		{
			return( varCode.to< InstanceOfMachine >().getRuntimeRID() );
		}
		return( varCode );
	}
	else if( varCode.is< InstanceOfData >() )
	{
		if( varCode.to< InstanceOfData >().isTypedMachine() )
		{
			return( varCode );
		}
	}

	return( BF::REF_NULL );
}

BF AvmcodeCompiler::decode_compileVariablePort(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	BF varCode = decode_compileExpression(aCTX, aCode);
	if( varCode.is< InstanceOfPort >() )
	{
		return( varCode );
	}
	else if( varCode.is< InstanceOfData >() )
	{
		if( varCode.to< InstanceOfData >().isTypedPort() )
		{
			return( varCode );
		}
	}

	return( BF::REF_NULL );
}

BF AvmcodeCompiler::decode_compileVariableBuffer(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	BF varCode = decode_compileExpression(aCTX, aCode);
	if( varCode.is< InstanceOfBuffer >() )
	{
		return( varCode );
	}
	else if( varCode.is< InstanceOfData >() )
	{
		if( varCode.to< InstanceOfData >().isTypedBuffer() )
		{
			return( varCode );
		}
	}

	return( BF::REF_NULL );
}




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the OPTIMIZER of EXPRESSION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BF AvmcodeCompiler::optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasInstruction() )
	{
		return( aCode );
	}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "in<expr>: "
			<< STRIML( aCode->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )


	BF expr = AVMCODE_COMPILER_TABLE[ aCode->getOpOffset() ]->
			optimizeExpression(aCTX, aCode);


AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "out:> "
			<< STRIML( expr.toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	return( expr );
}


BF AvmcodeCompiler::decode_optimizeExpression(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( optimizeExpression(aCTX, aCode.bfCode()) );
		}

		case FORM_INSTANCE_DATA_KIND:
		{
			const InstanceOfData & anInstance = aCode.to< InstanceOfData >();
			if( anInstance.getModifier().hasModifierPublicFinalStatic()
				&& anInstance.isTypedEnum() && anInstance.hasValue() )
			{
				return( anInstance.getValue() );
			}
			else
			{
				BF optExpr = aCode;

				return( optExpr );
			}
		}

		default:
		{
			BF optExpr = aCode;

			return( optExpr );
		}
	}
}




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the COMPILER of STATEMENT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeCompiler::compileStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "in<stmnt>: "
			<< STRIML( aCode->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;

//	AVM_OS_TRACE << "aCode->getOperator()   :> " << aCode->getOperator()->strOp()
//			<< std::endl
//			<< "aCode->getOpOffset()   :> " << aCode->getOpOffset()
//			<< std::endl
//			<< "AVMCODE_COMPILER_TABLE :> @" << &AVMCODE_COMPILER_TABLE
//			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )


	BFCode stmnt = AVMCODE_COMPILER_TABLE[ aCode->getOpOffset() ]->
			compileStatement(aCTX, aCode);


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "out:> "
			<< STRIML( stmnt->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )

	return( stmnt );
}


BF AvmcodeCompiler::decode_compileStatement(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( compileStatement(aCTX, aCode.bfCode()) );
		}

		case FORM_UFI_KIND:
		{
			return( compileUFI(aCTX, aCode.to< UniFormIdentifier>()) );
		}

		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			if( aCode.str().find(':') != std::string::npos )
			{
				return( compileFullyQualifiedNameID(aCTX, aCode) );
			}
			else
			{
				return( compileQualifiedIdentifier(aCTX, aCode) );
			}
		}
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( compileQualifiedIdentifier(aCTX, aCode) );
		}

		case FORM_XFSP_DATATYPE_KIND:
		{
			return( compileDataType(aCTX, aCode) );
		}

		case FORM_TYPE_SPECIFIER_KIND:
		{
			return( aCode );
		}

		case FORM_XFSP_VARIABLE_KIND:
		{
			return( compileVariable(aCTX, aCode) );
		}

		case FORM_XFSP_MACHINE_KIND:
		case FORM_XFSP_SYSTEM_KIND:
		{
			return( compileMachine(aCTX, aCode) );
		}

//		case FORM_XFSP_INSTANCE_KIND:
//		{
//			return( compileInstance(aCTX, aCode) );
//		}

		case FORM_XFSP_BUFFER_KIND:
		{
			return( compileBuffer(aCTX, aCode) );
		}

		case FORM_XFSP_PORT_KIND:
		{
			return( compilePort(aCTX, aCode) );
		}

		case FORM_XFSP_TRANSITION_KIND:
		{
			return( compileTransition(aCTX, aCode) );
		}

		case FORM_XFSP_ROUTINE_KIND:
		{
			return( compileRoutine(aCTX, aCode) );
		}


		case FORM_XFSP_PACKAGE_KIND:
		case FORM_XFSP_CHANNEL_KIND:
		case FORM_XFSP_COM_POINT_KIND:
		case FORM_XFSP_COM_ROUTE_KIND:
		case FORM_XFSP_CONNECTOR_KIND:

		case FORM_OPERATOR_KIND:

		case FORM_EXECUTABLE_MACHINE_KIND:

		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		case FORM_INSTANCE_DATA_KIND:
		case FORM_INSTANCE_MACHINE_KIND:
		case FORM_INSTANCE_PORT_KIND:

		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		case FORM_BUILTIN_STRING_KIND:
		{
			return( aCode );
		}

		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:
		case FORM_ARRAY_STRING_KIND:
		{
			return( aCode );
		}

		case FORM_ARRAY_IDENTIFIER_KIND:
		{
			ArrayIdentifier * idArray = aCode.to_ptr< ArrayIdentifier >();
			BFVector array;

			for( std::size_t index = 0; index < idArray->size() ; ++index )
			{
				array.append( compileIdentifier(aCTX, idArray->get(index)) );
			}

			return( BuiltinArray::create(array) );
		}

		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			ArrayQualifiedIdentifier * ufiArray =
					aCode.to_ptr< ArrayQualifiedIdentifier >();
			BFVector array;

			for( std::size_t index = 0; index < ufiArray->size() ; ++index )
			{
				array.append( compileFullyQualifiedNameID(
						aCTX, ufiArray->get(index)) );
			}

			return( BuiltinArray::create(array) );
		}

		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * bfarray = aCode.to_ptr< ArrayBF >();
			BFVector array;

			for( std::size_t index = 0; index < bfarray->size() ; ++index )
			{
				array.append( decode_compileExpression(
						aCTX, bfarray->at(index) ) );
			}

			return( BuiltinArray::create(array) );
		}


		case FORM_AVMTRANSITION_KIND:
		{
			return( aCode );
		}


		default:
		{ // TODO
			AVM_OS_WARNING_ALERT
					<< "AvmcodeCompiler is trying to decode_compileStatement"
					"\n\t<< " << aCode.str() << " >> !!!"
					<< SEND_ALERT;

			return( BF::REF_NULL );
		}
	}

	return( aCode );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the OPTIMIZER of << RUNTIME >> EXPRESSION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmcodeCompiler::optimizeEvalExpression(
		COMPILE_CONTEXT * aCTX, BFCode & aCode)
{
	if( aCode->hasInstruction() )
	{
		return( true );
	}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "in<expr>: "
			<< STRIML( aCode->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	BF expr = AVMCODE_COMPILER_TABLE[ aCode->getOpOffset() ]->
			optimizeExpression(aCTX, aCode);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "out:> "
			<< STRIML( expr.toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , COMPILING )

	if( expr.is< AvmCode >() )
	{
		aCode = expr.bfCode();

		return( true );

	}

	return( false );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the OPTIMIZER of STATEMENT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BFCode AvmcodeCompiler::optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BFCode & aCode)
{
	if( aCode->hasInstruction() )
	{
		return( aCode );
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )
	AVM_OS_TRACE << INCR_INDENT_TAB << "in<stmnt>: "
			<< STRIML( aCode->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;

//	AVM_OS_TRACE << "aCode->getOperator()   :> " << aCode->getOperator()->strOp()
//			<< std::endl
//			<< "aCode->getOpOffset()   :> " << aCode->getOpOffset()
//			<< std::endl
//			<< "AVMCODE_COMPILER_TABLE :> @" << &AVMCODE_COMPILER_TABLE
//			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )


	BFCode stmnt = AVMCODE_COMPILER_TABLE[ aCode->getOpOffset() ]->
			optimizeStatement(aCTX, aCode);


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )
	AVM_OS_TRACE << TAB_DECR_INDENT << "out:> "
			<< STRIML( stmnt->toString(AVM_OS_TRACE.INDENT) )
			<< std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMPILING )

	return( stmnt );
}


BF AvmcodeCompiler::decode_optimizeStatement(
		COMPILE_CONTEXT * aCTX, const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			return( optimizeStatement(aCTX, aCode.bfCode()) );
		}

		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		{
			optimizeProgramRoutine( const_cast< AvmProgram & >(
					aCode.to< AvmProgram >() ));

			return( aCode );
		}

		default:
		{
			BF optCode = aCode;

			return( optCode );
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the COMPILER of ROUTINE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


AvmProgram * AvmcodeCompiler::compileRoutineStructure(
		const BaseCompiler & aCompiler,
		AvmProgram & aProgramCtx, const Routine & aRoutine)
{
	const PropertyPart & aPropertyPart = aRoutine.getPropertyPart();
	
	std::size_t paramCount = aPropertyPart.getVariableParametersCount();
	std::size_t returnCount = aPropertyPart.getVariableReturnsCount();
	std::size_t paramReturnCount = paramCount + returnCount;

	AvmProgram * aCompiledRoutine = new AvmProgram(
			Specifier::SCOPE_ROUTINE_KIND, (& aProgramCtx),
			aRoutine, paramReturnCount );

	aCompiledRoutine->setParamOffsetCount(0, paramCount);
	aCompiledRoutine->setReturnOffsetCount(paramCount, returnCount);


	InstanceOfData * anInstance = nullptr;
	TypeSpecifier bfTS;

	std::size_t offset = 0;

	// Parameters
	BFVector::const_ref_iterator< Variable > itVar =
			aPropertyPart.getVariableParameters().begin();
	for( ; offset < paramCount ; ++itVar , ++offset )
	{
		bfTS = aCompiler.compileTypeSpecifier(aProgramCtx, itVar->getType());
		if( bfTS.invalid() )
		{
			bfTS = TypeManager::UNIVERSAL;

//			incrErrorCount();
			++AVM_ERROR_COUNT;

			AVM_OS_ERROR_ALERT << "AvmcodeCompiler::compileRoutine : << "
					<< itVar->strTypeSpecifier() << " >> !!!"
					<< SEND_ALERT;
		}

		anInstance = new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE,
				aCompiledRoutine, itVar, bfTS, offset);

		aCompiledRoutine->setVariable(offset, anInstance);

		if( itVar->hasValue() )
		{
			anInstance->setValue(
					decode_compileExpression(
							aProgramCtx, itVar->getValue()) );
		}
	}

	// Returns
	itVar = aPropertyPart.getVariableReturns().begin();
	for( ; offset < paramReturnCount ; ++itVar , ++offset )
	{
		bfTS = aCompiler.compileTypeSpecifier(aProgramCtx, itVar->getType());
		if( bfTS.invalid() )
		{
			bfTS = TypeManager::UNIVERSAL;

//			incrErrorCount();
			++AVM_ERROR_COUNT;

			AVM_OS_ERROR_ALERT << "AvmcodeCompiler::compileRoutine : << "
					<< itVar->strTypeSpecifier() << " >> !!!"
					<< SEND_ALERT;
		}

		anInstance = new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE,
				aCompiledRoutine, itVar, bfTS, offset);

		aCompiledRoutine->setVariable(offset, anInstance);

		if( itVar->hasValue() )
		{
			anInstance->setValue(
					decode_compileExpression(aProgramCtx, itVar->getValue()) );
		}
	}

	// Finalize compiled data
	aCompiledRoutine->updateVariableTable();

	return( aCompiledRoutine );
}


AvmProgram * AvmcodeCompiler::compileRoutine(const BaseCompiler & aCompiler,
		AvmProgram & aProgramCtx, const Routine & aRoutine)
{
	AvmProgram * aCompiledRoutine =
			compileRoutineStructure(aCompiler, aProgramCtx, aRoutine);

	// Compile Routine -> Code
	aCompiledRoutine->setCode(
			compileStatement((* aCompiledRoutine), aRoutine.getCode()) );

	return( aCompiledRoutine );
}


AvmProgram * AvmcodeCompiler::compileRoutine(
		const BaseCompiler & aCompiler, AvmProgram & aProgramCtx,
		InstanceOfData * aVarInstanceCtx, const Routine & aRoutine)
{
	AvmProgram * aCompiledRoutine =
			compileRoutineStructure(aCompiler, aProgramCtx, aRoutine);


	// Compile Routine -> Code
	CompilationEnvironment compilENV(aCompiledRoutine, aVarInstanceCtx);

	aCompiledRoutine->setCode(
			compileStatement(compilENV.mCTX, aRoutine.getCode()) );

	return( aCompiledRoutine );
}


AvmProgram * AvmcodeCompiler::compileRoutine(
		const BaseCompiler & aCompiler, AvmProgram & aProgramCtx,
		const TypeSpecifier & aTypeSpecifierCtx, const Routine & aRoutine)
{
	AvmProgram * aCompiledRoutine =
			compileRoutineStructure(aCompiler, aProgramCtx, aRoutine);

	// Compile Routine -> Code
	aCompiledRoutine->setCode(
			compileStatement(*aCompiledRoutine, aRoutine.getCode()) );

	return( aCompiledRoutine );
}


/**
 *******************************************************************************
 * POST-COMPILATION OF DATA ROUTINE
 *******************************************************************************
 */

void AvmcodeCompiler::optimizeDataRoutine(AvmProgram & aProgram)
{
//AVM_OS_TRACE << TAB << "<| optimizing<program>: "
//		<< aProgram.getFullyQualifiedNameID() << std::endl;

	if( aProgram.hasConstVariable() )
	{
		TableOfInstanceOfData::ref_iterator itVar =
				aProgram.getConstVariable().begin();
		TableOfInstanceOfData::ref_iterator endVar =
				aProgram.getConstVariable().end();
		for( ; itVar != endVar ; ++itVar )
		{
			/*
			 * initial macro value
			 */
			if( (itVar)->getModifier().hasNatureMacro()
				&& (itVar)->hasValue()
				&& (itVar)->getValue().is< AvmCode >() )
			{
				(itVar)->setValue( optimizeExpression(
						aProgram, (itVar)->getValue().bfCode()) );
			}
		}
	}

	if( aProgram.hasVariable() )
	{
		TableOfInstanceOfData::ref_iterator itVar =
				aProgram.getAllVariables().begin();
		TableOfInstanceOfData::ref_iterator endVar =
				aProgram.getAllVariables().end();
		for( ; itVar != endVar ; ++itVar )
		{
			/*
			 * initial macro value
			 */
			if( (itVar)->getModifier().hasNatureMacro()
				&& (itVar)->hasValue()
				&& (itVar)->getValue().is< AvmCode >() )
			{
				(itVar)->setValue( optimizeExpression(
						aProgram, (itVar)->getValue().bfCode()) );
			}

			/*
			 * onWrite
			 */
			if( (itVar)->hasOnWriteRoutine())
			{
				optimizeProgramRoutine( * (itVar)->getOnWriteRoutine() );
			}
		}
	}

	if( aProgram.hasVariableAlias() )
	{
		TableOfInstanceOfData::const_raw_iterator itVar =
				aProgram.getVariableAlias().begin();
		TableOfInstanceOfData::const_raw_iterator endVar =
				aProgram.getVariableAlias().end();
		for( ; itVar != endVar ; ++itVar )
		{
			/*
			 * Symbolic Array Index
			 */
			if( (itVar)->hasArrayIndexPointer() )
			{
				TableOfSymbol::iterator itDP = (itVar)->getDataPath()->begin();
				TableOfSymbol::iterator endItDP = (itVar)->getDataPath()->end();

				for( ; itDP != endItDP ; ++itDP )
				{
					if( (*itDP).isFieldArrayIndexPointer()
						&& (*itDP).getValue().is< AvmCode >() )
					{
						(*itDP).setValue( optimizeExpression(
								aProgram, (*itDP).getValue().bfCode()) );
					}
				}
			}
		}
	}


//AVM_OS_TRACE << TAB << ">| optimizing<Program>: "
//		<< aProgram.getFullyQualifiedNameID() << std::endl << std::endl;
}


void AvmcodeCompiler::optimizeDataRoutine(ExecutableForm & theExecutable)
{
//AVM_OS_TRACE << TAB << "<| optimizing<executable>: "
//		<< theExecutable.getFullyQualifiedNameID() << std::endl;

	optimizeDataRoutine( static_cast< AvmProgram & >(theExecutable) );

//AVM_OS_TRACE << TAB << ">| optimizing<executable>: "
//		<< theExecutable.getFullyQualifiedNameID() << std::endl << std::endl;
}



void AvmcodeCompiler::optimizeProgramRoutine(AvmProgram & aProgram)
{
//AVM_OS_TRACE << TAB << "<| optimizing<program>: "
//		<< aProgram.getFullyQualifiedNameID() << std::endl;


	/*
	 * onRead / onWrite routine of data
	 */
	optimizeDataRoutine( aProgram );


	if( aProgram.hasCode() )
	{
		aProgram.setCode( optimizeStatement(aProgram, aProgram.getCode()) );

		aProgram.updateOpcodeFamily();
	}


	/*
	 * onSynchronize
	 */
//	if( aProgram.hasOnSynchronize() )
//	{
//		aProgram.setOnSynchronize(
//				theAvmcodeCompiler.optimizeStatement(
//						aProgram, aProgram.getOnSynchronize()) );
//	}


//AVM_OS_TRACE << TAB << ">| optimizing<program>: "
//		<< aProgram.getFullyQualifiedNameID() << std::endl << std::endl;
}



void AvmcodeCompiler::optimizeInstance(
		ExecutableForm & theExecutableContainer, InstanceOfMachine * anInstance)
{
	ExecutableForm * anExec = anInstance->getExecutable();

	/*
	 * onCreate
	 */
	if( anInstance->hasOnCreate() )
	{
		CompilationEnvironment compilENV(nullptr,
				anExec, (& theExecutableContainer) );

		anInstance->setOnCreate( optimizeStatement(
				compilENV.mCTX, anInstance->getOnCreate() ) );
	}
	else
	{
		anInstance->setOnCreate( anExec->getOnCreate() );
	}

	/*
	 * onStart
	 */
	if( anInstance->hasOnStart() )
	{
		CompilationEnvironment compilENV(nullptr,
				anExec, (& theExecutableContainer) );

		anInstance->setOnStart( optimizeStatement(
				compilENV.mCTX, anInstance->getOnStart() ) );
	}
	else if( anExec->hasOnStart() )
	{
		anInstance->setOnStart( anExec->getOnStart() );
	}
	else if( anInstance->getSpecifier().hasDesignInstanceDynamic()
		|| anExec->getSpecifier().isComponentProcedure() )
	{
		if( anExec->hasOnInit() )
		{
			anInstance->setOnStart( anExec->getOnInit() );
		}
		else if( anInstance->getSpecifier().hasDesignInstanceDynamic() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "optimizeInstance: Unexpected #dynamic instance "
							"without << onStart Primitive >> !!!"
					<< std::endl << to_stream( anInstance )
					<< SEND_EXIT;
		}
	}

	//!![MIGRATION] optimizeInstanceParameter
	if( anInstance->hasParam() )
	{
		CompilationEnvironment compilENV(nullptr,
				anExec, (& theExecutableContainer) );
		COMPILE_CONTEXT * aCTX;

		InstanceOfData * paramVar;

		TableOfData::iterator it = anInstance->getParamReturnTable()->begin();
		TableOfData::iterator endIt = anInstance->getParamReturnTable()->end();
		for( avm_offset_t offset = 0 ; it != endIt ; ++it , ++offset )
		{
			if( (*it).is< AvmCode >() )
			{
				paramVar = anExec->rawParamVariable(offset);

				aCTX = compilENV.mCTX->clone( paramVar->getTypeSpecifier() );

				(*it) = optimizeExpression(aCTX, (*it).bfCode());

//				if( paramVar->getModifier().hasNatureReference()
//					&& (*it).is< AvmCode >() )
//				{
////				setArgcodeLValue(aCTX,
////					(*it).to< AvmCode >().getGlobalArgcode(), (*it));
//				}
			}
			else if( (*it).is< InstanceOfData >() )
			{
				const InstanceOfData & anInstance = (*it).to< InstanceOfData >();
				if( anInstance.getModifier().hasModifierPublicFinalStatic()
					&& anInstance.isTypedEnum() && anInstance.hasValue() )
				{
					(*it) = anInstance.getValue();
				}
			}
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// replace UFI by INSTANCE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


BF AvmcodeCompiler::substituteUfiByInstance(ExecutableForm & theExecutable,
		const BF & anElement, ListOfSymbol & usingInstance)
{
	if( anElement.invalid() )
	{
		return( anElement );
	}
	else if( anElement.is< Machine >() )
	{
		TableOfSymbol::const_iterator itMachine =
				theExecutable.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				theExecutable.instance_static_end();
		for(  ; itMachine != endMachine ; ++itMachine )
		{
			if( anElement.isTEQ( (*itMachine).safeAstElement() ) )
			{
				usingInstance.append( (*itMachine) );

				return( (*itMachine) );
			}
		}

		AVM_OS_EXIT( FAILED )
				<< "Undefined machine instance < "
				<< anElement.to< Machine >().getFullyQualifiedNameID()
				<< " > in executable machine < "
				<< theExecutable.getFullyQualifiedNameID() << " > !!!"
				<< SEND_EXIT;

		return( anElement );
	}
	else if( anElement.is< UniFormIdentifier >() )
	{
		std::string strUFI = anElement.str();

		TableOfSymbol::const_iterator itMachine =
				theExecutable.instance_static_begin();
		TableOfSymbol::const_iterator endMachine =
				theExecutable.instance_static_end();
		for(  ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).getAstFullyQualifiedNameID().find(strUFI,
					(*itMachine).getFullyQualifiedNameID().size()
						- strUFI.size()) != std::string::npos )
			{
				usingInstance.append( (*itMachine) );

				return( (*itMachine) );
			}
		}

		AVM_OS_EXIT( FAILED )
		<< "Undefined machine instance < "
				<< strUFI << " > in executable machine < "
				<< theExecutable.getFullyQualifiedNameID() << " > !!!"
				<< SEND_EXIT;

		return( anElement );
	}
	else if( anElement.is< AvmCode >() )
	{
		BFCode aCode = anElement.bfCode();
		BFCode aNewCode(aCode.getOperator());

		for( const auto & itOperand : aCode.getOperands() )
		{
			aNewCode->append( substituteUfiByInstance(
					theExecutable, itOperand, usingInstance) );
		}

		return( aNewCode );
	}
	else
	{
		return( anElement );
	}
}


}
