/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmPrimitiveProcessor.h"

#include <computer/ExecutionEnvironment.h>

#include <computer/primitive/BaseAvmPrimitive.h>

#include <computer/primitive/AvmActivityPrimitive.h>
#include <computer/primitive/AvmAssignPrimitive.h>
#include <computer/primitive/AvmBitwisePrimitive.h>
#include <computer/primitive/AvmBufferPrimitive.h>
#include <computer/primitive/AvmCommunicationPrimitive.h>
#include <computer/primitive/AvmConcurrencyPrimitive.h>
#include <computer/primitive/AvmCtorPrimitive.h>
#include <computer/primitive/AvmExpressionPrimitive.h>
#include <computer/primitive/AvmGuardPrimitive.h>
#include <computer/primitive/AvmInputEnabledPrimitive.h>
#include <computer/primitive/AvmInvokePrimitive.h>
#include <computer/primitive/AvmItePrimitive.h>
#include <computer/primitive/AvmIterationPrimitive.h>
#include <computer/primitive/AvmJumpPrimitive.h>
#include <computer/primitive/AvmLookupPrimitive.h>
#include <computer/primitive/AvmMathPrimitive.h>
#include <computer/primitive/AvmMetaPrimitive.h>
#include <computer/primitive/AvmSchedulingPrimitive.h>
#include <computer/primitive/AvmSequencePrimitive.h>
#include <computer/primitive/AvmStatusPrimitive.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <computer/instruction/InstructionEnvironment.h>

#include <fml/common/ObjectElement.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>

#include <fml/runtime/RuntimeDef.h>
#include <fml/runtime/RuntimeLib.h>

#include <sew/SymbexEngine.h>


namespace sep
{


/**
 * DESTRUCTOR
 */
AvmPrimitiveProcessor::~AvmPrimitiveProcessor()
{
	for( const auto & itPrimitive : AVM_PRIMITIVE_TABLE )
	{
		if( (itPrimitive != DEFAULT_AVM_PRIMITIVE) &&
			(itPrimitive != DEFAULT_INVOKE_ROUTINE) &&
			(itPrimitive != DEFAULT_EVAL_EXPRESSION_ALU) )
		{
			delete( itPrimitive );
		}
	}

	delete( DEFAULT_AVM_PRIMITIVE );
	delete( DEFAULT_INVOKE_ROUTINE );
	delete( DEFAULT_EVAL_EXPRESSION_ALU );
}


/**
 * GETTER
 * Builder
 * Loader
 */
Builder & AvmPrimitiveProcessor::getBuilder()
{
	return( mSymbexEngine.getBuilder() );
}

Loader & AvmPrimitiveProcessor::getLoader()
{
	return( mSymbexEngine.getLoader() );
}



/**
 * CONFIGURE
 */
bool AvmPrimitiveProcessor::configure()
{
	DEFAULT_AVM_PRIMITIVE = new BaseAvmPrimitive( *this );

	DEFAULT_INVOKE_ROUTINE = new AvmPrimitive_InvokeRoutine( *this );

	DEFAULT_EVAL_EXPRESSION_ALU = new AvmPrimitive_EvalExpressionALU( *this );

	AVM_PRIMITIVE_TABLE.resize(
			OperatorManager::TABLE_OF_OPERATOR.size(),
			DEFAULT_AVM_PRIMITIVE);

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

	if( not configureConcurrencyPrimitive() )
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

	if( not configureStringPrimitive() )
	{
		return( false );
	}

	if( not configureIoltPrimitive() )
	{
		return( false );
	}

	return( true );
}



#define OPCODE_COMPUTER( OPID )   \
		AVM_PRIMITIVE_TABLE[ OperatorManager::OPERATOR_##OPID->getOffset() ]

#define SET_OPCODE_COMPUTER( OPID , CLASS )   \
		AVM_PRIMITIVE_TABLE[ OperatorManager::OPERATOR_##OPID->getOffset() ] = new CLASS(*this)




bool AvmPrimitiveProcessor::configureOther()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM NOP STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( NOP ) = new AvmPrimitive_Nop( *this );


	////////////////////////////////////////////////////////////////////////////
	// AVM UFI STATEMENT
	////////////////////////////////////////////////////////////////////////////
//	OPCODE_COMPUTER( UFI ) = mAvmUfiPrimitive = new AvmPrimitive_Ufi( *this );


	////////////////////////////////////////////////////////////////////////////
	// AVM FORM CONSTRUCTOR STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( CTOR ) = new AvmPrimitive_Ctor( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureMeta()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM META STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( INFORMAL  ) = new AvmPrimitive_Informal( *this );

	OPCODE_COMPUTER( TRACE     ) = new AvmPrimitive_Trace( *this );

	OPCODE_COMPUTER( DEBUG     ) = new AvmPrimitive_Debug( *this );

	OPCODE_COMPUTER( COMMENT   ) = new AvmPrimitive_Comment( *this );

	OPCODE_COMPUTER( QUOTE     ) = new AvmPrimitive_Quote( *this );

	OPCODE_COMPUTER( META_EVAL ) = new AvmPrimitive_MetaEval( *this );
	OPCODE_COMPUTER( META_RUN  ) = new AvmPrimitive_MetaRun( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureLambdaPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// LAMBDA STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( APPLY  ) = DEFAULT_AVM_PRIMITIVE;

	OPCODE_COMPUTER( LAMBDA ) = DEFAULT_AVM_PRIMITIVE;


	////////////////////////////////////////////////////////////////////////////
	// LET STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( LET    ) = DEFAULT_AVM_PRIMITIVE;


	return( true );
}


bool AvmPrimitiveProcessor::configureActivityPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE SELF
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( SELF ) = new AvmPrimitive_Self( *this );

	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE MANAGING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( CONTEXT_SWITCHER ) = new AvmPrimitive_ContextSwitcher( *this );

	OPCODE_COMPUTER( PROCESS_STATE_SET) = new AvmPrimitive_ProcessStateSet( *this );

	OPCODE_COMPUTER( INIT        ) = new AvmPrimitive_Init( *this );
	OPCODE_COMPUTER( FINAL       ) = new AvmPrimitive_Final( *this );
	OPCODE_COMPUTER( DESTROY     ) = new AvmPrimitive_Destroy( *this );

	OPCODE_COMPUTER( START       ) = new AvmPrimitive_Start( *this );
	OPCODE_COMPUTER( RESTART     ) = new AvmPrimitive_Restart( *this );
	OPCODE_COMPUTER( STOP        ) = new AvmPrimitive_Stop( *this );

	OPCODE_COMPUTER( WAIT        ) = new AvmPrimitive_Wait( *this );

	OPCODE_COMPUTER( SUSPEND     ) = new AvmPrimitive_Suspend( *this );
	OPCODE_COMPUTER( RESUME      ) = new AvmPrimitive_Resume( *this );


	OPCODE_COMPUTER( IENABLE_INVOKE  ) = new AvmPrimitive_IEnableInvoke( *this );
	OPCODE_COMPUTER( ENABLE_INVOKE   ) = new AvmPrimitive_EnableInvoke( *this );
	OPCODE_COMPUTER( ENABLE_SET      ) = new AvmPrimitive_EnableSet( *this );

	OPCODE_COMPUTER( IDISABLE_INVOKE ) = new AvmPrimitive_IDisableInvoke( *this );
	OPCODE_COMPUTER( DISABLE_INVOKE  ) = new AvmPrimitive_DisableInvoke( *this );
	OPCODE_COMPUTER( DISABLE_SET     ) = new AvmPrimitive_DisableSet( *this );
	OPCODE_COMPUTER( DISABLE_CHILD   ) = new AvmPrimitive_DisableChild( *this );
	OPCODE_COMPUTER( DISABLE_SELF    ) = new AvmPrimitive_DisableSelf( *this );
	OPCODE_COMPUTER( DISABLE_SELVES  ) = new AvmPrimitive_DisableSelves( *this );

	OPCODE_COMPUTER( IABORT_INVOKE   ) = new AvmPrimitive_IAbortInvoke( *this );
	OPCODE_COMPUTER( ABORT_INVOKE    ) = new AvmPrimitive_AbortInvoke( *this );
	OPCODE_COMPUTER( ABORT_SET       ) = new AvmPrimitive_AbortSet( *this );
	OPCODE_COMPUTER( ABORT_CHILD     ) = new AvmPrimitive_AbortChild( *this );
	OPCODE_COMPUTER( ABORT_SELF      ) = new AvmPrimitive_AbortSelf( *this );
	OPCODE_COMPUTER( ABORT_SELVES    ) = new AvmPrimitive_AbortSelves( *this );

	OPCODE_COMPUTER( HISTORY_CLEAR          ) = new AvmPrimitive_HistoryClear( *this );
	OPCODE_COMPUTER( DEEP_HISTORY_INVOKE    ) = new AvmPrimitive_DeepHistoryInvoke( *this );
	OPCODE_COMPUTER( SHALLOW_HISTORY_INVOKE ) = new AvmPrimitive_ShallowHistoryInvoke( *this );

	OPCODE_COMPUTER( IRUN  ) = new AvmPrimitive_IRun( *this );
	OPCODE_COMPUTER( RUN   ) = new AvmPrimitive_Run( *this );

	OPCODE_COMPUTER( RTC   ) = new AvmPrimitive_Rtc( *this );


	OPCODE_COMPUTER( INVOKE_NEW         ) = new AvmPrimitive_InvokeNew( *this );

	OPCODE_COMPUTER( INVOKE_ROUTINE     ) = DEFAULT_INVOKE_ROUTINE;

	OPCODE_COMPUTER( INVOKE_TRANSITION  ) = new AvmPrimitive_InvokeTransition( *this );

	OPCODE_COMPUTER( INVOKE_METHOD   ) = new AvmPrimitive_InvokeMethod( *this );
	OPCODE_COMPUTER( INVOKE_PROGRAM  ) = new AvmPrimitive_InvokeProgram( *this );
	OPCODE_COMPUTER( INVOKE_FUNCTION ) = new AvmPrimitive_InvokeFunction( *this );

	OPCODE_COMPUTER( INVOKE_LAMBDA_APPLY ) = new AvmPrimitive_InvokeLambdaApply( *this );
	OPCODE_COMPUTER( INVOKE_LAMBDA_LET   ) = new AvmPrimitive_InvokeLambdaLet( *this );


	OPCODE_COMPUTER( SCHEDULE_INVOKE ) = new AvmPrimitive_ScheduleInvoke( *this );
	OPCODE_COMPUTER( SCHEDULE_GET    ) = new AvmPrimitive_ScheduleGet( *this );
	OPCODE_COMPUTER( SCHEDULE_IN     ) = new AvmPrimitive_ScheduleIn( *this );
	OPCODE_COMPUTER( SCHEDULE_SET    ) = new AvmPrimitive_ScheduleSet( *this );

	OPCODE_COMPUTER( DEFER_INVOKE ) = new AvmPrimitive_DeferInvoke( *this );
	OPCODE_COMPUTER( DEFER_GET    ) = new AvmPrimitive_DeferGet( *this );
	OPCODE_COMPUTER( DEFER_SET    ) = new AvmPrimitive_DeferSet( *this );

	OPCODE_COMPUTER( GOTO ) = new AvmPrimitive_Goto( *this );

	OPCODE_COMPUTER( FORK ) = new AvmPrimitive_Fork( *this );
	OPCODE_COMPUTER( JOIN ) = new AvmPrimitive_Join( *this );

	OPCODE_COMPUTER( INPUT_ENABLED ) = new AvmPrimitive_InputEnabled( *this );

	OPCODE_COMPUTER( RDV  ) = new AvmPrimitive_Rdv( *this );

	OPCODE_COMPUTER( SYNCHRONIZE ) = new AvmPrimitive_Synchronize( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureStatusPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MACHINE STATUS
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( STATUS_WAS   ) = new AvmPrimitive_StatusWas( *this );
	OPCODE_COMPUTER( STATUS_IS    ) = new AvmPrimitive_StatusIs( *this );
	OPCODE_COMPUTER( STATUS_BEING ) = new AvmPrimitive_StatusBeing( *this );
	OPCODE_COMPUTER( STATUS_WILL  ) = new AvmPrimitive_StatusWill( *this );

	OPCODE_COMPUTER( CHANGED      ) = new AvmPrimitive_Changed( *this );
	OPCODE_COMPUTER( CHANGED_TO   ) = new AvmPrimitive_ChangedTo( *this );

	return( true );
}


bool AvmPrimitiveProcessor::configureConcurrencyPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM PROGRAM SCHEDULING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( ASYNCHRONOUS       ) = new AvmPrimitive_Asynchronous( *this );
	OPCODE_COMPUTER( STRONG_SYNCHRONOUS ) = new AvmPrimitive_StrongSynchronous( *this );
	OPCODE_COMPUTER( WEAK_SYNCHRONOUS   ) = new AvmPrimitive_WeakSynchronous( *this );
	OPCODE_COMPUTER( INTERLEAVING       ) = new AvmPrimitive_Interleaving( *this );
	OPCODE_COMPUTER( PARTIAL_ORDER      ) = new AvmPrimitive_PartialOrder( *this );
	OPCODE_COMPUTER( PARALLEL           ) = new AvmPrimitive_Parallel( *this );

	OPCODE_COMPUTER( RDV_ASYNCHRONOUS       ) = new AvmPrimitive_RdvAsynchronous( *this );
	OPCODE_COMPUTER( RDV_STRONG_SYNCHRONOUS ) = new AvmPrimitive_RdvStrongSynchronous( *this );
	OPCODE_COMPUTER( RDV_WEAK_SYNCHRONOUS   ) = new AvmPrimitive_RdvWeakSynchronous( *this );
	OPCODE_COMPUTER( RDV_INTERLEAVING       ) = new AvmPrimitive_RdvInterleaving( *this );
	OPCODE_COMPUTER( RDV_PARTIAL_ORDER      ) = new AvmPrimitive_RdvPartialOrder( *this );
	OPCODE_COMPUTER( RDV_PARALLEL           ) = new AvmPrimitive_RdvParallel( *this );


	OPCODE_COMPUTER( EXCLUSIVE      ) = new AvmPrimitive_Exclusive( *this );
	OPCODE_COMPUTER( NONDETERMINISM ) = new AvmPrimitive_Nondeterminism( *this );

	OPCODE_COMPUTER( PRIOR_GT       ) = new AvmPrimitive_Prior( *this );
	OPCODE_COMPUTER( PRIOR_LT       ) = new AvmPrimitive_Prior( *this );

	OPCODE_COMPUTER( SCHEDULE_AND_THEN ) = new AvmPrimitive_ScheduleAndThen( *this );
	OPCODE_COMPUTER( SCHEDULE_OR_ELSE  ) = new AvmPrimitive_ScheduleOrElse( *this );

	OPCODE_COMPUTER( ATOMIC_SEQUENCE ) = new AvmPrimitive_AtomicSequence( *this );
	OPCODE_COMPUTER( SEQUENCE        ) = new AvmPrimitive_Sequence( *this );
	OPCODE_COMPUTER( SEQUENCE_SIDE   ) = new AvmPrimitive_SideSequence( *this );
	OPCODE_COMPUTER( SEQUENCE_WEAK   ) = new AvmPrimitive_WeakSequence( *this );

	OPCODE_COMPUTER( PRODUCT         ) = new AvmPrimitive_Product( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureBasicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM BUFFER MANAGING
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( UPDATE_BUFFER ) = new AvmPrimitive_UpdateBuffer( *this );


	////////////////////////////////////////////////////////////////////////////
	// AVM PRIMITIVE STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( ASSIGN        ) = new AvmPrimitive_Assignment( *this );
	OPCODE_COMPUTER( ASSIGN_AFTER  ) = new AvmPrimitive_AssignmentAfter( *this );
	OPCODE_COMPUTER( ASSIGN_OP_AFTER ) = new AvmPrimitive_AssignmentOpAfter( *this );

	OPCODE_COMPUTER( ASSIGN_REF    ) = new AvmPrimitive_AssignmentRef( *this );
	OPCODE_COMPUTER( ASSIGN_MACRO  ) = new AvmPrimitive_AssignmentMacro( *this );

	OPCODE_COMPUTER( ASSIGN_NEWFRESH ) = new AvmPrimitive_AssignNewFresh( *this );

	OPCODE_COMPUTER( ASSIGN_RESET    ) = new AvmPrimitive_AssignReset( *this );

	OPCODE_COMPUTER( GUARD         ) = new AvmPrimitive_Guard( *this );
	OPCODE_COMPUTER( TIMED_GUARD   ) = new AvmPrimitive_TimedGuard( *this );

	OPCODE_COMPUTER( EVENT         ) = new AvmPrimitive_Event( *this );
	OPCODE_COMPUTER( CHECK_SAT     ) = new AvmPrimitive_CheckSat( *this );


	OPCODE_COMPUTER( INPUT            ) = new AvmPrimitive_Input( *this );
	OPCODE_COMPUTER( INPUT_FROM       ) = new AvmPrimitive_InputFrom( *this );
	// Optimized version of INPUT
	OPCODE_COMPUTER( INPUT_VAR        ) = new AvmPrimitive_InputVar( *this );
	OPCODE_COMPUTER( INPUT_ENV        ) = new AvmPrimitive_InputEnv( *this );
	OPCODE_COMPUTER( INPUT_BUFFER     ) = new AvmPrimitive_InputBuffer( *this );
	OPCODE_COMPUTER( INPUT_RDV        ) = new AvmPrimitive_InputRdv( *this );

	OPCODE_COMPUTER( INPUT_FLOW       ) = new AvmPrimitive_Input( *this );
	OPCODE_COMPUTER( INPUT_BROADCAST  ) = new AvmPrimitive_Input( *this );
	OPCODE_COMPUTER( INPUT_DELEGATE   ) = new AvmPrimitive_Input( *this );


	OPCODE_COMPUTER( OUTPUT           ) = new AvmPrimitive_Output( *this );
	OPCODE_COMPUTER( OUTPUT_TO        ) = new AvmPrimitive_OutputTo( *this );
	// Optimized version of OUTPUT
	OPCODE_COMPUTER( OUTPUT_VAR       ) = new AvmPrimitive_OutputVar( *this );
	OPCODE_COMPUTER( OUTPUT_ENV       ) = new AvmPrimitive_OutputEnv( *this );
	OPCODE_COMPUTER( OUTPUT_BUFFER    ) = new AvmPrimitive_OutputBuffer( *this );
	OPCODE_COMPUTER( OUTPUT_RDV       ) = new AvmPrimitive_OutputRdv( *this );

	OPCODE_COMPUTER( OUTPUT_FLOW      ) = new AvmPrimitive_Output( *this );
	OPCODE_COMPUTER( OUTPUT_BROADCAST ) = new AvmPrimitive_Output( *this );
	OPCODE_COMPUTER( OUTPUT_DELEGATE  ) = new AvmPrimitive_Output( *this );


	OPCODE_COMPUTER( PRESENT       ) = new AvmPrimitive_Present( *this );
	OPCODE_COMPUTER( ABSENT        ) = new AvmPrimitive_Absent( *this );

	OPCODE_COMPUTER( IF            ) = new AvmPrimitive_If( *this );
	OPCODE_COMPUTER( IFE           ) = new AvmPrimitive_Ife( *this );

	OPCODE_COMPUTER( FOR           ) = new AvmPrimitive_For( *this );
	OPCODE_COMPUTER( FOREACH       ) = new AvmPrimitive_Foreach( *this );
	OPCODE_COMPUTER( WHILE_DO      ) = new AvmPrimitive_WhileDo( *this );
	OPCODE_COMPUTER( DO_WHILE      ) = new AvmPrimitive_DoWhile( *this );

	OPCODE_COMPUTER( BREAK         ) = new AvmPrimitive_Break( *this );
	OPCODE_COMPUTER( CONTINUE      ) = new AvmPrimitive_Continue( *this );
	OPCODE_COMPUTER( RETURN        ) = new AvmPrimitive_Return( *this );
	OPCODE_COMPUTER( EXIT          ) = new AvmPrimitive_Exit( *this );

	OPCODE_COMPUTER( STEP_MARK     ) = new AvmPrimitive_StepMark( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureBitwisePrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM BITWISE EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPUTER( BNOT   ) = new AvmPrimitive_BNOT( *this );

	OPCODE_COMPUTER( BAND   ) = new AvmPrimitive_BAND( *this );
	OPCODE_COMPUTER( BOR    ) = new AvmPrimitive_BOR( *this );
	OPCODE_COMPUTER( BXOR   ) = new AvmPrimitive_BXOR( *this );

	OPCODE_COMPUTER( LSHIFT ) = new AvmPrimitive_LSHIFT( *this );
	OPCODE_COMPUTER( RSHIFT ) = new AvmPrimitive_RSHIFT( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureLogicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM PREDICAT EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPUTER( NOT      ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( AND      ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( AND_THEN ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( NAND     ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( XAND     ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( OR       ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( OR_ELSE  ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( NOR      ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( XOR      ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( XNOR     ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( IMPLIES  ) = DEFAULT_EVAL_EXPRESSION_ALU;


	////////////////////////////////////////////////////////////////////////////
	// AVM COMPARISON EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPUTER( EQ   ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( NEQ  ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( SEQ  ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( NSEQ ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( LT   ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( LTE  ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( GT   ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( GTE  ) = DEFAULT_EVAL_EXPRESSION_ALU;


	return( true );
}


bool AvmPrimitiveProcessor::configureArithmeticPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM ARITHMETIC EXPRESSION
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPUTER( PLUS   ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( MINUS  ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( UMINUS ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( MULT   ) = DEFAULT_EVAL_EXPRESSION_ALU;
	OPCODE_COMPUTER( POW    ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( DIV    ) = DEFAULT_EVAL_EXPRESSION_ALU;

	OPCODE_COMPUTER( MOD    ) = new AvmPrimitive_MOD( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureLookupPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// LOOKUP STATEMENT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( LOOKUP_INT       ) = new AvmPrimitive_Lookup_Int( *this );

	OPCODE_COMPUTER( LOOKUP_INT_EXT   ) = new AvmPrimitive_Lookup_IntExt( *this );

	OPCODE_COMPUTER( LOOKUP_NEAREST   ) = new AvmPrimitive_Lookup_Nearest( *this );

	OPCODE_COMPUTER( LOOKUP_BELOW     ) = new AvmPrimitive_Lookup_Below( *this );

	OPCODE_COMPUTER( LOOKUP_ABOVE     ) = new AvmPrimitive_Lookup_Above( *this );


	OPCODE_COMPUTER( LOOKUP2D_INT_EXT ) = new AvmPrimitive_Lookup2D_IntExt( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureMathematicPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM MATHEMATICAL FUNCTION
	////////////////////////////////////////////////////////////////////////////

	// MIN - MAX
	OPCODE_COMPUTER( MIN ) = new AvmPrimitive_MIN( *this );
	OPCODE_COMPUTER( MAX ) = new AvmPrimitive_MAX( *this );

	// RANDOM
	OPCODE_COMPUTER( RANDOM ) = new AvmPrimitive_RANDOM( *this );

	// ABS
	OPCODE_COMPUTER( ABS ) = new AvmPrimitive_ABS( *this );

	// ROUNDING
	OPCODE_COMPUTER( CEIL     ) = new AvmPrimitive_CEIL( *this );
	OPCODE_COMPUTER( FLOOR    ) = new AvmPrimitive_FLOOR( *this );
	OPCODE_COMPUTER( ROUND    ) = new AvmPrimitive_ROUND( *this );
	OPCODE_COMPUTER( TRUNCATE ) = new AvmPrimitive_TRUNCATE( *this );


	// EXP - LOG
	OPCODE_COMPUTER( SQRT ) = new AvmPrimitive_SQRT( *this );

	OPCODE_COMPUTER( EXP  ) = new AvmPrimitive_EXP( *this );
	OPCODE_COMPUTER( LOG  ) = new AvmPrimitive_LOG( *this );

	// TRIGONOMETRIC
	OPCODE_COMPUTER( SIN ) = new AvmPrimitive_SIN( *this );
	OPCODE_COMPUTER( COS ) = new AvmPrimitive_COS( *this );
	OPCODE_COMPUTER( TAN ) = new AvmPrimitive_TAN( *this );

	OPCODE_COMPUTER( SINH ) = new AvmPrimitive_SINH( *this );
	OPCODE_COMPUTER( COSH ) = new AvmPrimitive_COSH( *this );
	OPCODE_COMPUTER( TANH ) = new AvmPrimitive_TANH( *this );

	OPCODE_COMPUTER( ASIN  ) = new AvmPrimitive_ASIN( *this );
	OPCODE_COMPUTER( ACOS  ) = new AvmPrimitive_ACOS( *this );
	OPCODE_COMPUTER( ATAN  ) = new AvmPrimitive_ATAN( *this );
	OPCODE_COMPUTER( ATAN2 ) = new AvmPrimitive_ATAN2( *this );

	OPCODE_COMPUTER( ASINH ) = new AvmPrimitive_ASINH( *this );
	OPCODE_COMPUTER( ACOSH ) = new AvmPrimitive_ACOSH( *this );
	OPCODE_COMPUTER( ATANH ) = new AvmPrimitive_ATANH( *this );

	return( true );
}


bool AvmPrimitiveProcessor::configureStringPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// AVM STRING / COLLECTION OPERATOR
	////////////////////////////////////////////////////////////////////////////

	OPCODE_COMPUTER( CONTAINS ) = new AvmPrimitive_CONTAINS( *this );

	OPCODE_COMPUTER( IN    ) = new AvmPrimitive_IN( *this );
	OPCODE_COMPUTER( NOTIN ) = new AvmPrimitive_NOTIN( *this );

	OPCODE_COMPUTER( SUBSET    ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( SUBSETEQ  ) = DEFAULT_AVM_PRIMITIVE;

	OPCODE_COMPUTER( INTERSECT ) = DEFAULT_AVM_PRIMITIVE;

	OPCODE_COMPUTER( STARTS_WITH ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( ENDS_WITH   ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( CONCAT      ) = DEFAULT_AVM_PRIMITIVE;


	OPCODE_COMPUTER( APPEND ) = new AvmPrimitive_APPEND( *this );
	OPCODE_COMPUTER( REMOVE ) = new AvmPrimitive_REMOVE( *this );
	OPCODE_COMPUTER( CLEAR  ) = new AvmPrimitive_CLEAR( *this );
	OPCODE_COMPUTER( RESIZE ) = new AvmPrimitive_RESIZE( *this );

	OPCODE_COMPUTER( PUSH       ) = new AvmPrimitive_PUSH( *this );
	OPCODE_COMPUTER( ASSIGN_TOP ) = new AvmPrimitive_ASSIGN_TOP( *this );
	OPCODE_COMPUTER( TOP        ) = new AvmPrimitive_TOP( *this );
	OPCODE_COMPUTER( POP        ) = new AvmPrimitive_POP( *this );
	OPCODE_COMPUTER( POP_FROM   ) = new AvmPrimitive_POP_FROM( *this );

	OPCODE_COMPUTER( EMPTY     ) = new AvmPrimitive_EMPTY( *this );
	OPCODE_COMPUTER( NONEMPTY  ) = new AvmPrimitive_NONEMPTY( *this );
	OPCODE_COMPUTER( SINGLETON ) = new AvmPrimitive_SINGLETON( *this );
	OPCODE_COMPUTER( POPULATED ) = new AvmPrimitive_POPULATED( *this );
	OPCODE_COMPUTER( FULL      ) = new AvmPrimitive_FULL( *this );

	OPCODE_COMPUTER( SIZE      ) = new AvmPrimitive_SIZE( *this );


	return( true );
}


bool AvmPrimitiveProcessor::configureIoltPrimitive()
{
	////////////////////////////////////////////////////////////////////////////
	// IOLTL BEHAVIORAL PREDICAT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( GLOBALLY   ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( UNTIL      ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( NEXT       ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( EVENTUALLY ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( RELEASES   ) = DEFAULT_AVM_PRIMITIVE;

	OPCODE_COMPUTER( OBS        ) = new AvmPrimitive_OBS( *this );


	////////////////////////////////////////////////////////////////////////////
	// IOLTL LOGICAL PREDICAT
	////////////////////////////////////////////////////////////////////////////
	OPCODE_COMPUTER( AND_T ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( OR_T  ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( NOT_T ) = DEFAULT_AVM_PRIMITIVE;
	OPCODE_COMPUTER( IMP_T ) = DEFAULT_AVM_PRIMITIVE;


	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// TOOLS for POST-RUN
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


void AvmPrimitiveProcessor::postRun(
		ExecutionContext & anEC, ListOfExecutionData & runEDS)
{
	if( runEDS.nonempty() )
	{
		std::uint32_t nHeight = anEC.getHeight() + 1;
		std::uint32_t aWidth  = anEC.getWidth();

		for( auto & itED : runEDS )
		{
			switch( itED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				{
					if( not itED.hasRunnableElementTrace() )
					{
						//!! NOTHING
						break;
					}

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				default:
				{
//					if( ((*itED).getExecutionContext() ==
//										theED.getExecutionContext())
//							/* || (not (*itED).hasExecutionContext()) */ )
					{
						anEC.appendChildContext(
							new ExecutionContext(anEC, itED, nHeight, aWidth) );
					}
					break;
				}
			}
		}
	}
}

void AvmPrimitiveProcessor::postRun(
		ExecutionContext & anEC, ExecutionEnvironment & ENV)
{
	postRun(anEC, ENV.outEDS);

	postRun(anEC, ENV.exitEDS);

	postRun(anEC, ENV.irqEDS);
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the INIT statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

void AvmPrimitiveProcessor::init(ExecutionContext & anEC)
{
AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
	ObjectElement::USE_ONLY_ID = true;
AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )

//	anEC.writeTraceBeforeExec(AVM_OS_TRACE);
//	anEC.writeTraceBeforeExec(AVM_OS_COUT);

	// SAVE AND UNSET THE ASSIGN TABLE
	BF aNodeCondition;
	BF aNodeTimedCondition;
	BF aRunnableElementTrace;
	BF aIOElementTrace;
	TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag;

//	anEC.resetDataBeforeEvaluation();
	anEC.getwExecutionData().storeVariantBeforeEvaluation(
			aNodeCondition, aNodeTimedCondition,
			aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);

	ExecutionEnvironment ENV(*this, (& anEC));

	if( ENV.run(ENV.inED.getOnInit()) )
	{
	}

	// POST-RUN
	postRun(anEC, ENV);

	// RESTORE THE ASSIGN TABLE
//	anEC.restoreDataAfterEvaluation();
	anEC.getwExecutionData().restoreVariantAfterEvaluation(
			aNodeCondition, aNodeTimedCondition,
			aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);


//	anEC.writeTraceAfterExec(AVM_OS_TRACE);
//	anEC.writeTraceAfterExec(AVM_OS_COUT);

AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
	ObjectElement::USE_ONLY_ID = false;
AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )

}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// the RUN statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * the RUN statement
 */
void AvmPrimitiveProcessor::run(ExecutionContext & anEC)
{
AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
	ObjectElement::USE_ONLY_ID = true;
AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )

//	anEC.writeTraceBeforeExec(AVM_OS_TRACE);
//	anEC.writeTraceBeforeExec(AVM_OS_COUT);

	// SAVE AND UNSET THE ASSIGN TABLE
	BF aNodeCondition;
	BF aNodeTimedCondition;
	BF aRunnableElementTrace;
	BF aIOElementTrace;
	TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag;

//	anEC.resetDataBeforeEvaluation();
	anEC.getwExecutionData().storeVariantBeforeEvaluation(
			aNodeCondition, aNodeTimedCondition,
			aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);


	ExecutionEnvironment ENV(*this, (& anEC));

	switch( ENV.inED.getAEES() )
	{
		case AEES_STEP_MARK:
		{
			ENV.inED.mwsetAEES(AEES_STEP_RESUME);

			if( decode_resume( ENV ) )
			{
			}

			break;
		}

		case AEES_STMNT_NOTHING:
		case AEES_STMNT_FINAL:
		case AEES_STMNT_DESTROY:
		{
			if( not ENV.inED.isFinalizedOrDestroyed(ENV.inED.getSystemRID()) )
			{
				ENV.inED.mwsetAEES(AEES_OK);
			}

			[[fallthrough]]; //!! No BREAK for that CASE statement
		}

		case AEES_OK:
		{
			ENV.inED.setSystemRID();
			if( ENV.inED.getOnSchedule()->noOperand() &&
				(ENV.inED.getOnSchedule()->isOpCode(AVM_OPCODE_SCHEDULE_INVOKE)) )
			{
				if( ENV.run(ENV.inED.getSystemRuntime().getOnSchedule()) )
				{
				}
			}
			else if( ENV.run(ENV.inED.getOnSchedule()) )
			{
			}

			break;
		}

		case AEES_WAITING_JOIN_FORK:
		case AEES_STMNT_EXIT:
		case AEES_STMNT_EXIT_ALL:
		case AEES_STMNT_FATAL_ERROR:
		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			break;
		}

		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		case AEES_STMNT_RETURN:
		case AEES_STEP_RESUME:

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected an input Execution Context for running"
						" with the AVM EXECECUTION ENDING STATUS << "
					<< RuntimeDef::strAEES( ENV.inED.getAEES() ) << " >> !!!"
					<< SEND_EXIT;
			break;
		}
	}

	// POST-RUN
	postRun(anEC, ENV);


	// RESTORE THE ASSIGN TABLE
//	anEC.restoreDataAfterEvaluation();
	anEC.getwExecutionData().restoreVariantAfterEvaluation(
			aNodeCondition, aNodeTimedCondition,
			aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);


//	anEC.writeTraceAfterExec(AVM_OS_TRACE);
//	anEC.writeTraceAfterExec(AVM_OS_COUT);


AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
	ObjectElement::USE_ONLY_ID = false;
AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
}


void AvmPrimitiveProcessor::run(ExecutionContext & anEC, const BF & aRunnableElement)
{
	AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
		ObjectElement::USE_ONLY_ID = true;
	AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )

	//	anEC.writeTraceBeforeExec(AVM_OS_TRACE);
	//	anEC.writeTraceBeforeExec(AVM_OS_COUT);

		// SAVE AND UNSET THE ASSIGN TABLE
		BF aNodeCondition;
		BF aNodeTimedCondition;
		BF aRunnableElementTrace;
		BF aIOElementTrace;
		TableOfRuntimeFormState::TableOfAssignedFlag aTableOfAssignedFlag;

	//	anEC.resetDataBeforeEvaluation();
		anEC.getwExecutionData().storeVariantBeforeEvaluation(
				aNodeCondition, aNodeTimedCondition,
				aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);


		ExecutionEnvironment ENV(*this, (& anEC));


		if( ENV.run(aRunnableElement) )
		{
		}

		// POST-RUN
		postRun(anEC, ENV);


		// RESTORE THE ASSIGN TABLE
	//	anEC.restoreDataAfterEvaluation();
		anEC.getwExecutionData().restoreVariantAfterEvaluation(
				aNodeCondition, aNodeTimedCondition,
				aRunnableElementTrace, aIOElementTrace, aTableOfAssignedFlag);


	//	anEC.writeTraceAfterExec(AVM_OS_TRACE);
	//	anEC.writeTraceAfterExec(AVM_OS_COUT);


	AVM_IF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
		ObjectElement::USE_ONLY_ID = false;
	AVM_ENDIF_DEBUG_NOT_FLAG( QUALIFIED_NAME_ID )
}



static bool isDebugProgram(const Operator * anOperator)
{
	switch( anOperator->getAvmOpCode() )
	{
		/*
		 ***********************************************************************
		 * AVM MACHINE ACTIVITY
		 ***********************************************************************
		 */
		case AVM_OPCODE_CONTEXT_SWITCHER:

		case AVM_OPCODE_INIT:
		case AVM_OPCODE_FINAL:
		case AVM_OPCODE_DESTROY:

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		case AVM_OPCODE_STOP:

		case AVM_OPCODE_WAIT:

		case AVM_OPCODE_SUSPEND:
		case AVM_OPCODE_RESUME:

		case AVM_OPCODE_IENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:

		case AVM_OPCODE_IDISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_DISABLE_SET:

		case AVM_OPCODE_DISABLE_CHILD:
		case AVM_OPCODE_DISABLE_SELF:
		case AVM_OPCODE_DISABLE_SELVES:

		case AVM_OPCODE_IABORT_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		case AVM_OPCODE_ABORT_SET:

		case AVM_OPCODE_ABORT_CHILD:
		case AVM_OPCODE_ABORT_SELF:
		case AVM_OPCODE_ABORT_SELVES:

		case AVM_OPCODE_HISTORY_CLEAR:
		case AVM_OPCODE_DEEP_HISTORY_INVOKE:
		case AVM_OPCODE_SHALLOW_HISTORY_INVOKE:

		case AVM_OPCODE_IRUN:
		case AVM_OPCODE_RUN:

		case AVM_OPCODE_RTC:

		case AVM_OPCODE_SCHEDULE_INVOKE:
		case AVM_OPCODE_SCHEDULE_GET:
		case AVM_OPCODE_SCHEDULE_SET:

		case AVM_OPCODE_DEFER_INVOKE:
		case AVM_OPCODE_DEFER_GET:
		case AVM_OPCODE_DEFER_SET:

		case AVM_OPCODE_FORK:
		case AVM_OPCODE_JOIN:

		case AVM_OPCODE_RDV:

		case AVM_OPCODE_INPUT_ENABLED:

		case AVM_OPCODE_SYNCHRONIZE:

		case AVM_OPCODE_INVOKE_NEW:


		/*
		 ***********************************************************************
		 * AVM PROGRAM SCHEDULING
		 ***********************************************************************
		 */
		case AVM_OPCODE_ASYNCHRONOUS:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		case AVM_OPCODE_INTERLEAVING:
		case AVM_OPCODE_PARALLEL:

		case AVM_OPCODE_EXCLUSIVE:

		case AVM_OPCODE_NONDETERMINISM:


		case AVM_OPCODE_PRIOR_GT:
		case AVM_OPCODE_PRIOR_LT:

//		case AVM_OPCODE_ATOMIC_SEQUENCE:
//
//		case AVM_OPCODE_SEQUENCE:
//		case AVM_OPCODE_SEQUENCE_SIDE:
//		case AVM_OPCODE_SEQUENCE_WEAK:
//
//		case AVM_OPCODE_PRODUCT:

		/*
		 ***********************************************************************
		 * LAMBDA STATEMENT
		 ***********************************************************************
		 */
//		case AVM_OPCODE_APPLY:
//
//		case AVM_OPCODE_LAMBDA:
//
//		case AVM_OPCODE_INVOKE_ROUTINE:

		case AVM_OPCODE_INVOKE_TRANSITION:

		case AVM_OPCODE_INVOKE_METHOD:
		case AVM_OPCODE_INVOKE_PROGRAM:
		case AVM_OPCODE_INVOKE_FUNCTION:

//		case AVM_OPCODE_INVOKE_LAMBDA_APPLY:
//		case AVM_OPCODE_INVOKE_LAMBDA_LET:

		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}






bool AvmPrimitiveProcessor::run(avm_offset_t opOffset, ExecutionEnvironment & ENV)
{
	const AvmCode * aCode = ENV.inCODE;

	if( aCode == nullptr )
	{
		return( false );
	}

AVM_IF_DEBUG_FLAG_AND( COMPUTING , AVM_DEBUG_FLAG_OR( STATEMENT,
		AVM_DEBUG_FLAG_AND( PROGRAM ,
				isDebugProgram(aCode->getOperator()) ) ) )

		AVM_OS_TRACE << INCR_INDENT_TAB << "<< "
				<< ENV.inED.getRID().strUniqId() << " |=> ";
		aCode->toStream( AVM_OS_TRACE << IGNORE_FIRST_TAB );

	AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
		ENV.inED.toStreamData(AVM_OS_TRACE);
	AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

	AVM_IF_DEBUG_LEVEL_GT_HIGH
		AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "<< "
				<< ENV.inED.getRID().strUniqId() << " |=> ";
		aCode->toStream( AVM_OS_COUT << IGNORE_FIRST_TAB );
	AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_FLAG_AND( COMPUTING  )


	bool rtCode = false;

	try
	{
		if( ENV.inCODE->hasInstruction() )
		{
			InstructionEnvironment INSTRUCTION_ENV(ENV);
			if( (ENV.mARG = INSTRUCTION_ENV.itARG)
					->main_decode_eval_args(ENV.inCODE.to< AvmCode >()) )
			{
//				while( ENV.mARG != nullptr )
				{
					ENV.inED = ENV.mARG->outED;

					rtCode = AVM_PRIMITIVE_TABLE[ opOffset ]->run(ENV) || rtCode;

//				ENV.mARG = INSTRUCTION_ENV.itARG = INSTRUCTION_ENV.itARG->NEXT;
				}
			}
		}
		else
		{
			rtCode = AVM_PRIMITIVE_TABLE[ opOffset ]->run(ENV);
		}
	}
	catch( const AvmExitException & aee )
	{
		// TODO !!!
//		avm_set_exit_code( aee.mExitCode );
	}
	catch( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"AvmPrimitiveProcessor::run< std::exception >",
				e.what(), '*', 80);
	}
	catch( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS( "AvmPrimitiveProcessor::"
				"run< unknown::exception > !!!", '*', 80);
	}


AVM_IF_DEBUG_FLAG_AND( COMPUTING , AVM_DEBUG_FLAG_OR( STATEMENT,
		AVM_DEBUG_FLAG_AND( PROGRAM ,
				isDebugProgram(aCode->getOperator()) ) ) )

	AVM_IF_DEBUG_LEVEL_GTE_HIGH

		AVM_OS_TRACE << TAB_DECR_INDENT
				<< ">> " << ENV.inED.getRID().strUniqId()
				<< " |=> " <<  aCode->str() << std::endl;

		AVM_IF_DEBUG_FLAG( DATA )
			ENV.inED.toStreamData(AVM_OS_TRACE);
		AVM_ENDIF_DEBUG_FLAG( DATA )

		AVM_IF_DEBUG_LEVEL_GT_HIGH
			AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "  >> "
					<< ENV.inED.getRID().strUniqId()
					<< " |=> " << aCode->str() << std::endl;
		AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

		AVM_OS_TRACE << std::flush;

	AVM_DEBUG_ELSE

		AVM_OS_TRACE << DECR_INDENT;

	AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_FLAG_AND( COMPUTING )

	return( rtCode );
}


bool AvmPrimitiveProcessor::invokeRoutine(ExecutionEnvironment & ENV,
		AvmProgram * aRoutine, const BF & aParam)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<< "
			<< ENV.inED.getRID().strUniqId() << " |=> invoke#routine "
			<< aRoutine->getFullyQualifiedNameID() << " " << aParam.str() << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
		ENV.inED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
		AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "<< "
				<< ENV.inED.getRID().strUniqId()
				<< " |=> invoke#routine " << aRoutine->getFullyQualifiedNameID()
				<< " " << aParam.str() << std::flush;
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

	bool rtCode = ( aRoutine->hasParam() )
			? DEFAULT_INVOKE_ROUTINE->run(ENV, *aRoutine, aParam)
			: DEFAULT_INVOKE_ROUTINE->run(ENV, *aRoutine);


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << TAB_DECR_INDENT << ">> "
				<< ENV.inED.getRID().strUniqId() << " |=> invoke#routine "
				<<  aRoutine->getFullyQualifiedNameID() << " " << aParam.str() << std::endl;

AVM_IF_DEBUG_FLAG( DATA )
			ENV.inED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
			AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "  >> "
					<< ENV.inED.getRID().strUniqId()
					<< " |=> invoke#routine " << aRoutine->getFullyQualifiedNameID()
					<< " " << aParam.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

		AVM_OS_TRACE << std::flush;

AVM_DEBUG_ELSE

		AVM_OS_TRACE << DECR_INDENT;

AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

	return( rtCode );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// the RESUME & EVAL statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitiveProcessor::resume(ExecutionEnvironment & ENV)
{
	const AvmCode * aCode = ENV.inCODE;

	if( aCode == nullptr )
	{
		return( false );
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<<|| pos:"
			<< static_cast< std::size_t >(
					ENV.inEXEC_LOCATION->itCode - aCode->begin())
//			<< " ?!? |=> " << aProgram->->str() << std::endl
			<< " " << ENV.inED.getRID().strUniqId() << " |=> ";
	aCode->toStream( AVM_OS_TRACE << IGNORE_FIRST_TAB );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
		ENV.inED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
		AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "<<|| "
				<< ENV.inED.getRID().strUniqId() << " |=> ";
		aCode->toStream( AVM_OS_COUT << IGNORE_FIRST_TAB );
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )


	bool rtCode = AVM_PRIMITIVE_TABLE[ aCode->getOpOffset() ]->resume(ENV);


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << TAB_DECR_INDENT << "||>> "
				<< ENV.inED.getRID().strUniqId()
				<< " |=> " <<  aCode->str() << std::endl;

AVM_IF_DEBUG_FLAG( DATA )
			ENV.inED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
			AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "  ||>> "
					<< ENV.inED.getRID().strUniqId()
					<< " |=> " << aCode->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

		AVM_OS_TRACE << std::flush;

AVM_DEBUG_ELSE

		AVM_OS_TRACE << DECR_INDENT;

AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

	return( rtCode );
}


bool AvmPrimitiveProcessor::decode_resume(ExecutionEnvironment & ENV)
{
	ExecutionData tmpED = ENV.inED;
	tmpED.makeWritable();
	tmpED.pushExecutionLocationhCache();

	ListOfExecutionData tmpListOfInputED( tmpED );

	ExecutionEnvironment tmpENV(ENV.PRIMITIVE_PROCESSOR);

	while( tmpListOfInputED.nonempty() )
	{
		tmpListOfInputED.pop_first_to( tmpED );

		if( not tmpENV.resume(ENV, tmpED) )
		{
			AVM_OS_EXIT( FAILED )
					<< "Failed to RESUME< STATEMENT >!!!"
					<< SEND_EXIT;

			return( false );
		}

		while( tmpENV.outEDS.nonempty() )
		{
			tmpENV.outEDS.pop_last_to( tmpED );

			switch( tmpED.getAEES() )
			{
				case AEES_STMNT_NOTHING:
				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:
				{
					tmpED.mwsetAEES( AEES_OK );

					[[fallthrough]]; //!! No BREAK for that CASE statement
				}

				case AEES_STEP_RESUME:
				{
					if( tmpED.hasExecutionLocation() )
					{
						tmpListOfInputED.append( tmpED );
					}
					else
					{
						tmpED.mwsetAEES( AEES_OK );
						ENV.outEDS.append( tmpED );
					}

					break;
				}

				case AEES_OK:
				case AEES_STMNT_RETURN:
				{
					if( tmpED.hasExecutionLocation() )
					{
						tmpListOfInputED.append( tmpED );
					}
					else
					{
						ENV.outEDS.append( tmpED );
					}

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES( tmpED.getAEES() ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}
	}

	// Sync EDS traitement
	while( tmpENV.syncEDS.nonempty() )
	{
		tmpENV.syncEDS.first().pushExecutionLocationhCache();

		ENV.appendSync( tmpENV.syncEDS.pop_first() );
	}

	// IRQ EDS traitement

	ENV.spliceNotOutput(tmpENV);

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// the DECODE & EVAL statement
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/**
 * the EVAL instruction
 */

bool AvmPrimitiveProcessor::seval(EvaluationEnvironment & ENV)
{
	const AvmCode * anExpression = ENV.inCODE;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
	AVM_OS_TRACE << INCR_INDENT_TAB << "<< "
			<< ENV.inED.getRID().strUniqId() << " , ED |-> ";
	anExpression->toStream( AVM_OS_TRACE << IGNORE_FIRST_TAB );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , DATA )
		ENV.outED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
		AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "<< ED |-> ";
		anExpression->toStream( AVM_OS_COUT << IGNORE_FIRST_TAB );
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

	AVM_OS_TRACE << std::flush;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )


	bool rtCode = false;
	if( ENV.inCODE->hasInstruction() )
	{
		switch( ENV.inCODE->getInstruction()->getMainContext() )
		{
			case AVM_ARG_STANDARD_CTX:
			{
				InstructionEnvironment INSTRUCTION_ENV(ENV);

				if( (ENV.mARG = INSTRUCTION_ENV.itARG)
						->main_decode_eval_args(ENV.inCODE.to< AvmCode >()) )
				{
					ENV.outED = ENV.mARG->outED;

					rtCode = AVM_PRIMITIVE_TABLE
							[anExpression->getOpOffset()]->seval(ENV);
				}
				break;
			}

			case AVM_ARG_ARGUMENT_CTX:
			case AVM_ARG_PARAMETER_CTX:
			case AVM_ARG_RETURN_CTX:
			{
				InstructionEnvironment INSTRUCTION_ENV(ENV, 1);

				if( (ENV.mARG = INSTRUCTION_ENV.itARG)
						->main_decode_eval(ENV.inCODE) )
				{
					ENV.outED = ENV.mARG->outED;
					ENV.outVAL = ENV.mARG->at(0);

					rtCode = true;
				}
				break;
			}

			case AVM_ARG_UNDEFINED_CONTEXT:
			default:
			{
				AVM_OS_FATAL_ERROR_EXIT
						<< "AvmPrimitiveProcessor::seval :> Unexpected "
							"opcode << " << ENV.inCODE->strDebug() << " >> !!!"
						<< SEND_EXIT;

				return( false );
			}
		}
	}
	else
	{
		rtCode = AVM_PRIMITIVE_TABLE[ anExpression->getOpOffset() ]->seval(ENV);
	}


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )
AVM_IF_DEBUG_LEVEL_GTE_HIGH
		AVM_OS_TRACE << TAB_DECR_INDENT << ">> "
				<< ENV.inED.getRID().strUniqId() << " , ED |-> "
				<<  anExpression->str() << std::endl;

AVM_IF_DEBUG_FLAG( DATA )
			ENV.inED.toStreamData(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_FLAG( DATA )

AVM_IF_DEBUG_LEVEL_GT_HIGH
			AVM_OS_COUT << AVM_OS_TRACE.INDENT.TABS << "  >> " <<
					ENV.inED.getRID().strUniqId() << " , ED |-> "
					<< anExpression->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GT_HIGH

		AVM_OS_TRACE << std::flush;

AVM_DEBUG_ELSE

		AVM_OS_TRACE << DECR_INDENT;

AVM_ENDIF_DEBUG_LEVEL_GTE_HIGH
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , COMPUTING , STATEMENT )

	return( rtCode );
}


bool AvmPrimitiveProcessor::seval_wrt_ARG(EvaluationEnvironment & ENV)
{
	return( AVM_PRIMITIVE_TABLE[ ENV.inCODE->getOpOffset() ]->seval(ENV) );
}


/**
 * the DECODE EVAL instruction
 */

bool AvmPrimitiveProcessor::decode_seval(EvaluationEnvironment & ENV)
{
	switch( ENV.inFORM.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			ENV.inCODE = ENV.inFORM.bfCode();

			return( seval(ENV) );
		}


		case FORM_INSTANCE_DATA_KIND:
		{
			const InstanceOfData & anInstance =
					ENV.inFORM.to< InstanceOfData >();

			if( (anInstance.getModifier().hasNatureReference()) )
			{
				ENV.outVAL = ENV.getRvalue(ENV.outED, ENV.getRvalue(
						ENV.outED, anInstance).to< InstanceOfData >() );
			}
			else if( (anInstance.getModifier().hasNatureMacro()) )
			{
				ENV.inFORM = ENV.getRvalue(ENV.outED, anInstance);

				return( decode_seval(ENV) );
			}
			else if( anInstance.getModifier().hasFeatureMutable() )
			{
				ENV.outVAL = ENV.getRvalue(ENV.outED, anInstance);
			}

			else if( anInstance.isEnumSymbolPointer() )
			{
				ENV.outVAL = ( anInstance.hasValue() &&
						(not anInstance.getModifier().hasFeatureUnsafe()) )
						? anInstance.getValue() : ENV.inFORM;
			}

			else if( ExecutableLib::MACHINE_SELF == anInstance )
			{
				ENV.outVAL = ENV.inED.getRID();
			}

			else if( ExecutableLib::MACHINE_PARENT == anInstance )
			{
				ENV.outVAL = ENV.inED.getRID().getPRID();
			}

			else
			{
				ENV.outVAL = ENV.inFORM;
			}

			return( true );
		}


		case FORM_BUILTIN_BOOLEAN_KIND:
		case FORM_BUILTIN_CHARACTER_KIND:
		case FORM_BUILTIN_INTEGER_KIND:
		case FORM_BUILTIN_RATIONAL_KIND:
		case FORM_BUILTIN_FLOAT_KIND:
		case FORM_BUILTIN_STRING_KIND:
		case FORM_BUILTIN_IDENTIFIER_KIND:
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:

		case FORM_OPERATOR_KIND:

		case FORM_AVMLAMBDA_KIND:
		case FORM_AVMPROGRAM_KIND:
		case FORM_AVMTRANSITION_KIND:
		case FORM_EXECUTABLE_MACHINE_KIND:
		case FORM_EXECUTABLE_SYSTEM_KIND:
		{
			ENV.outVAL = ENV.inFORM;

			return( true );
		}


//		case FORM_UFI_KIND:
//		{
//			return( mAvmUfiPrimitive->s_evalUfi(ENV, ENV.inFORM.bfUFI()) );
//		}

		case FORM_INSTANCE_MACHINE_KIND:
		{
			const InstanceOfMachine & anInstance =
					ENV.inFORM.to< InstanceOfMachine >();

			if( anInstance.hasRuntimeRID() )
			{
				ENV.outVAL = anInstance.getRuntimeRID();
			}

			else if( ExecutableLib::MACHINE_NULL == anInstance )
			{
				ENV.outVAL = RuntimeLib::RID_NIL;
			}

			else if( ExecutableLib::MACHINE_ENVIRONMENT == anInstance )
			{
				ENV.outVAL = RuntimeLib::RID_ENVIRONMENT;
			}

			else
			{
				ENV.outVAL = ENV.outED.getRuntimeID(anInstance);
			}

			return( true );
		}

		case FORM_RUNTIME_ID_KIND:

		case FORM_INSTANCE_PORT_KIND:
		case FORM_INSTANCE_BUFFER_KIND:
		case FORM_INSTANCE_CONNECTOR_KIND:
		{
			ENV.outVAL = ENV.inFORM;

			return( true );
		}


		case FORM_ARRAY_BOOLEAN_KIND:
		case FORM_ARRAY_INTEGER_KIND:
		case FORM_ARRAY_RATIONAL_KIND:
		case FORM_ARRAY_FLOAT_KIND:

		case FORM_ARRAY_CHARACTER_KIND:
		case FORM_ARRAY_IDENTIFIER_KIND:
		case FORM_ARRAY_STRING_KIND:
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			ENV.outVAL.renew( ENV.inFORM.to< BuiltinArray >().getArrayBF() );

			return( true );
		}


		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * inArray = ENV.inFORM.to_ptr< ArrayBF >();

			ArrayBF * outArrayBF = new ArrayBF(
					inArray->getTypeSpecifier(), inArray->size());

			for( std::size_t i = 0 ; i < inArray->size() ; ++i )
			{
				if( ENV.seval( inArray->at(i) ) )
				{
					outArrayBF->set(i, ENV.outVAL);
				}
				else
				{
					ENV.outVAL.renew( outArrayBF );

					return( false );
				}
			}

			ENV.outVAL.renew( outArrayBF );

			return( true );
		}


		default:
		{
			if( ENV.inFORM.is< BuiltinList >() )
			{
				BuiltinList * inContainer = ENV.inFORM.to_ptr< BuiltinList >();

				BuiltinList * outContainer = new BuiltinList(
						inContainer->classKind(), inContainer->capacity());

				BuiltinList::const_iterator it = inContainer->begin();
				BuiltinList::const_iterator endIt = inContainer->end();
				for( ; it != endIt ; ++it )
				{
					if( ENV.seval( *it ) )
					{
						outContainer->push(ENV.outVAL);
					}
					else
					{
						ENV.outVAL.renew( outContainer );

						return( false );
					}
				}

				ENV.outVAL.renew( outContainer );

				return( true );
			}

			else if( ENV.inFORM.is< BuiltinVector >() )
			{
				BuiltinVector * inContainer = ENV.inFORM.to_ptr< BuiltinVector >();

				BuiltinVector * outContainer = new BuiltinVector(
						inContainer->classKind(),
						((BuiltinContainer *)inContainer)->capacity());

				for( std::size_t i = 0 ; i < inContainer->size() ; ++i )
				{
					if( ENV.seval( inContainer->at(i) ) )
					{
						outContainer->push(ENV.outVAL);
					}
					else
					{
						ENV.outVAL.renew( outContainer );

						return( false );
					}
				}

				ENV.outVAL.renew( outContainer );

				return( true );
			}

			// TODO
			AVM_OS_WARNING_ALERT
					<< "AvmPrimitiveProcessor is trying "
						"to decode_seval the Expression\n"
					<< ENV.inFORM.toString( AVM_TAB1_INDENT )
					<< SEND_ALERT;

			ENV.outVAL = ENV.inFORM;

			return( false );
		}
	}

	return( true );
}




}
