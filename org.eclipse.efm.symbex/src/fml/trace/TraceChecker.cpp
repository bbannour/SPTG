/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceChecker.h"

#include <computer/EvaluationEnvironment.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstructorImpl.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/trace/TracePoint.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * TEST
 * TracePoint Nature
 */
bool TraceChecker::isPointNature(const BF & arg,
		ENUM_TRACE_POINT::TRACE_NATURE nature) const
{
	if( arg.is< TracePoint >() )
	{
		return( arg.to< TracePoint >().nature == nature );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// SAT CHECKING API
////////////////////////////////////////////////////////////////////////////////

bool TraceChecker::isSat(const ExecutionContext & anEC, const BF & arg)
{
	if( arg.is< TracePoint >() )
	{
		if( isSat(anEC, arg.to< TracePoint >()) )
		{
			return( true );
		}
	}
	else if( arg.is< AvmCode >() )
	{
		return( isSat(anEC, arg.to< AvmCode >()) );
	}

	return( false );
}


bool TraceChecker::isSat(const ExecutionContext & anEC, const AvmCode & aCode)
{
	switch( aCode.getAvmOpCode() )
	{
		case AVM_OPCODE_AND:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_AND_THEN:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not isSat(anEC, itOperand) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( isSat(anEC, itOperand) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_EXCLUSIVE:
		{
			std::size_t passCount = 0;

			for( const auto & itOperand : aCode.getOperands() )
			{
				if( isSat(anEC, itOperand) )
				{
					if( ++passCount > 1 )
					{
						return( false );
					}
				}
			}

			return( passCount == 1 );
		}


		case AVM_OPCODE_NOT:
		{
			return( not isSat(anEC, aCode.first()) );
		}


		case AVM_OPCODE_NAND:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( not isSat(anEC, itOperand) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_NOR:
		{
			for( const auto & itOperand : aCode.getOperands() )
			{
				if( isSat(anEC, itOperand) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_XNOR:
		{
			std::size_t passCount = 0;

			for( const auto & itOperand : aCode.getOperands() )
			{
				if( isSat(anEC, itOperand) )
				{
					if( ++passCount > 1 )
					{
						return( true );
					}
				}
			}

			return( passCount != 1 );
		}

		default:
		{
			return( false );
		}
	}
}


bool TraceChecker::isSat(
		const ExecutionContext & anEC, AVM_OPCODE anOp, const BF & arg)
{
	switch( anOp )
	{
		case AVM_OPCODE_AND:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_AND_THEN:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( not isSat(anEC, argArray->at(offset)) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( isSat(anEC, argArray->at(offset)) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_EXCLUSIVE:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			std::size_t passCount = 0;

			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( isSat(anEC, argArray->at(offset)) )
				{
					if( ++passCount > 1 )
					{
						return( false );
					}
				}
			}

			return( passCount == 1 );
		}


		case AVM_OPCODE_NOT:
		{
			return( not isSat(anEC, arg) );
		}


		case AVM_OPCODE_NAND:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( not isSat(anEC, argArray->at(offset)) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_NOR:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( isSat(anEC, argArray->at(offset)) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_XNOR:
		{
			std::size_t passCount = 0;

			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( isSat(anEC, argArray->at(offset)) )
				{
					if( ++passCount > 1 )
					{
						return( true );
					}
				}
			}

			return( passCount != 1 );
		}

		default:
		{
			return( false );
		}
	}
}



bool TraceChecker::isSat(const ExecutionContext & anEC, const TracePoint & aTP)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , SOLVING )
	AVM_OS_TRACE << "isSat ? EC:> " << anEC.str_min() << std::endl
			<< "Fired:> " << anEC.getRunnableElementTrace().str() << std::endl
			<< "Trace:> " << anEC.getIOElementTrace().str() << std::endl;
	AVM_OS_TRACE << "Point:>" << str_indent( aTP ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , SOLVING )


	switch( aTP.nature )
	{
		case ENUM_TRACE_POINT::TRACE_FORMULA_NATURE:
		case ENUM_TRACE_POINT::TRACE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_DECISION_NATURE:

		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:
		{
			return( isSatFormula(anEC, aTP) );
		}

		case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
		{
			if( aTP.op == AVM_OPCODE_ASSIGN_NEWFRESH )
			{
				return( isSatCom(anEC, aTP, anEC.getIOElementTrace()) );
			}
			else
			{
				return( isSatTime(anEC, aTP) );
			}
		}
		case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
		{
			if( aTP.op == AVM_OPCODE_ASSIGN_NEWFRESH )
			{
				return( isSatCom(anEC, aTP, anEC.getIOElementTrace()) );
			}
			else
			{
				return( isSatVariable(anEC, aTP) );
			}
		}

		case ENUM_TRACE_POINT::TRACE_COM_NATURE:
		case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
		case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
		case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
		{
			return( isSatCom(anEC, aTP, anEC.getIOElementTrace()) );
		}


		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:
		{
			return( isSatRunnable(anEC, aTP, anEC.getRunnableElementTrace()) );
		}

		case ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE:
		{
			return( isSatRoutine(anEC, aTP, anEC.getRunnableElementTrace()) );
		}

		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		{
			return( isSatTransition(anEC, aTP, anEC.getRunnableElementTrace()) );
		}

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		{
			return( isSatState(anEC, aTP, anEC.getRunnableElementTrace()) );
		}

		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		{
			return( isSatStatemachine(anEC, aTP, anEC.getRunnableElementTrace()) );
		}

		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			return( isSatMachine(anEC, aTP, anEC.getRunnableElementTrace()) );
		}


		case ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE:
		{
			return( isSat(anEC, aTP.op, aTP.value) );
		}

		default:
		{
			return( false );
		}
	}
}


bool TraceChecker::isSatFormula(const ExecutionContext & anEC, const TracePoint & aTP)
{
	if( ENV.evalFormula(anEC, theLocalExecutableForm, aTP.value) )
	{
		ENV.outVAL = ExpressionConstructorNative::andExpr(
				anEC.getExecutionData().getAllPathCondition(), ENV.outVAL );

		return( SolverFactory::isStrongSatisfiable(theSolverKind, ENV.outVAL) );
	}
	else
	{
		return( false );
	}
}


bool TraceChecker::isSatTime(const ExecutionContext & anEC, const TracePoint & aTP)
{
	return( true );
}

bool TraceChecker::isSatVariable(
		const ExecutionContext & anEC, const TracePoint & aTP)
{
	if( aTP.RID.invalid() )
	{
		const_cast< TracePoint & >(aTP).updateRID( anEC.getExecutionData() );
	}

	if( ENV.eval(anEC.getExecutionData(),
			anEC.getExecutionData().getSystemRID(), aTP.value) )
	{
		const BF & value = ( aTP.RID.valid() )
				? ENV.getRvalue(
						aTP.RID, aTP.object->to< InstanceOfData >() )
				: ENV.getRvalue( aTP.object->to< InstanceOfData >() );

		switch( aTP.op )
		{
			case AVM_OPCODE_SEQ:
			{
				return( ENV.outVAL.strEQ( value ) );
			}

			case AVM_OPCODE_CHECK_SAT:
			{
				if( ENV.outVAL.isEQ( value ) )
				{
					return( true );
				}

				if( aTP.object->to_ptr< InstanceOfData >()->isTypedBoolean() )
				{
					if( ENV.outVAL.isEqualTrue() )
					{
						ENV.outVAL = ExpressionConstructorNative::andExpr(
							value,
							anEC.getExecutionData().getAllPathCondition() );
					}
					else if( ENV.outVAL.isEqualFalse() )
					{
						ENV.outVAL = ExpressionConstructorNative::andExpr(
							ExpressionConstructorNative::notExpr(value),
							anEC.getExecutionData().getAllPathCondition() );
					}
					else
					{
						ENV.outVAL = ExpressionConstructorNative::andExpr(
							ExpressionConstructorNative::eqExpr(ENV.outVAL, value),
							anEC.getExecutionData().getAllPathCondition() );
					}
				}
				else
				{
					ENV.outVAL = ExpressionConstructorNative::andExpr(
						ExpressionConstructorNative::eqExpr(ENV.outVAL, value),
						anEC.getExecutionData().getAllPathCondition() );
				}

				return( SolverFactory::isStrongSatisfiable(
						theSolverKind, ENV.outVAL) );
			}

			case AVM_OPCODE_NOP:
			case AVM_OPCODE_NULL:
			{
				return( true );
			}

			case AVM_OPCODE_EQ:
			case AVM_OPCODE_ASSIGN:
			default:
			{
				return( ENV.outVAL.isEQ( value ) );
			}
		}
	}

	return( false );
}


bool TraceChecker::isSatCom(
		const ExecutionContext & anEC, const TracePoint & aTP, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return( false );
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmCode >() )
		{
			const AvmCode & ioCode = aConf.getCode().to< AvmCode >();

			if( (aTP.object == nullptr)
				|| (aTP.object == ioCode.first().raw_pointer()) )
			{
				switch( aTP.op )
				{
					case AVM_OPCODE_INPUT:
					case AVM_OPCODE_INPUT_ENV:
					case AVM_OPCODE_INPUT_FROM:
					case AVM_OPCODE_INPUT_RDV:
					case AVM_OPCODE_INPUT_MULTI_RDV:
					case AVM_OPCODE_INPUT_BUFFER:

					case AVM_OPCODE_OUTPUT:
					case AVM_OPCODE_OUTPUT_ENV:
					case AVM_OPCODE_OUTPUT_TO:
					case AVM_OPCODE_OUTPUT_RDV:
					case AVM_OPCODE_OUTPUT_MULTI_RDV:
					case AVM_OPCODE_OUTPUT_BUFFER:
					{
//						return( ioCode.isOpCode( aTP.op )
//								&& ( (aTP.machine == nullptr)
//									|| (not aConf.hasRuntimeID())
//									|| aConf.getRuntimeID().
//											hasAsAncestor(aTP.machine) ) );

						if( ioCode.isOpCode( aTP.op ) )
						{
							if( aTP.any_object )
							{
								return( true );
							}
							else if( aTP.RID.valid() )
							{
								return( aConf.getRuntimeID().hasAsAncestor(aTP.RID) );
							}
							else
							{
								return( (aTP.machine == nullptr)
										|| aTP.machine
												->getSpecifier().isDesignModel()
										|| aConf.getRuntimeID()
												.hasAsAncestor(* aTP.machine) );
							}
						}
						return( false );
					}

					case AVM_OPCODE_ASSIGN_NEWFRESH:
					{
						return( ioCode.isOpCode( aTP.op ) );
					}

					case AVM_OPCODE_NULL:
					{
						return( true );
					}

					default:
					{
						return( aTP.op == ioCode.getOptimizedOpCode() );
					}
				}
			}
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
		{
			if( isSatCom(anEC, aTP, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceChecker::isSatRunnable(
		const ExecutionContext & anEC, const TracePoint & aTP, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return( false );
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aTP.object != nullptr )
		{
			if( aConf.getCode().isnot< AvmProgram >()
				|| (aConf.getCode().to_ptr< AvmProgram >() != aTP.object) )
			{
				return( false );
			}
		}
		else if( aTP.op != AVM_OPCODE_NULL )
		{
			if( aConf.getCode().isnot< Operator >()
				|| aConf.getOperator().isnotOpCode(aTP.op) )
			{
				return( false );
			}
		}

		RuntimeID aRID = aConf.getRuntimeID();
		while( aRID.valid() && (aRID.getInstance() != aTP.machine) )
		{
			aRID = aRID.getPRID();
		}

		return( aRID.valid() );
	}
	else if( aTrace.is< AvmCode >() )
	{
		for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
		{
			if( isSatMachine(anEC, aTP, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceChecker::isSatRoutine(
		const ExecutionContext & anEC, const TracePoint & aTP, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return( false );
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aTP.object != nullptr )
		{
			if( aConf.getCode().isnot< AvmProgram >() ||
				(aConf.getCode().to_ptr< AvmProgram >() != aTP.object) )
			{
				return( false );
			}
		}
		else if( aTP.op != AVM_OPCODE_NULL )
		{
			if( aConf.getCode().isnot< Operator >()
				|| aConf.getOperator().isnotOpCode(aTP.op) )
			{
				return( false );
			}
		}

		RuntimeID aRID = aConf.getRuntimeID();
		while( aRID.valid() && (aRID.getInstance() != aTP.machine) )
		{
			aRID = aRID.getPRID();
		}

		return( aRID.valid() );
	}
	else if( aTrace.is< AvmCode >() )
	{
		for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
		{
			if( isSatMachine(anEC, aTP, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceChecker::isSatTransition(const ExecutionContext & anEC,
		const TracePoint & aTP, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return( false );
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< AvmTransition >() )
		{
			if( aTP.object == aConf.getCode().to_ptr< AvmTransition >() )
			{
				if( aTP.any_object )
				{
					return( true );
				}
				else if( aTP.RID.valid() )
				{
					return( aConf.getRuntimeID().hasAsAncestor(aTP.RID) );
				}
				else
				{
					return( (aTP.machine == nullptr)
							|| aTP.machine->getSpecifier().isDesignModel()
							|| aConf.getRuntimeID().hasAsAncestor(* aTP.machine) );
				}
			}
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		const AvmCode & aCode = aTrace.to< AvmCode >();

		for( const auto & itOperand : aCode.getOperands() )
		{
			if( isSatTransition(anEC, aTP, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceChecker::isSatState(const ExecutionContext & anEC,
		const TracePoint & aTP, const BF & aTrace)
{
	if( aTP.RID.invalid() )
	{
		const_cast< TracePoint & >(aTP).updateRID( anEC.getExecutionData() );
	}

	if( aTP.RID.valid() )
	{
		const ExecutionData & anED = anEC.getExecutionData();
		return( anED.isIdleOrRunning(aTP.RID)
				|| anED.isFinalizedOrDestroyed(aTP.RID)
				|| isSatMachine(anEC, aTP, aTrace) );
	}

	return( isSatMachine(anEC, aTP, aTrace) );
}


bool TraceChecker::isSatStatemachine(const ExecutionContext & anEC,
		const TracePoint & aTP, const BF & aTrace)
{
	if( aTP.RID.invalid() )
	{
		const_cast< TracePoint & >(aTP).updateRID( anEC.getExecutionData() );
	}

	if( aTP.RID.valid() )
	{
		return( anEC.getExecutionData().isIdleOrRunning(aTP.RID)
				|| isSatMachine(anEC, aTP, aTrace) );
	}

	return( isSatMachine(anEC, aTP, aTrace) );
}


bool TraceChecker::isSatMachine(
		const ExecutionContext & anEC, const TracePoint & aTP, const BF & aTrace)
{
	if( aTrace.invalid() )
	{
		return( false );
	}
	else if( aTrace.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & aConf =
				aTrace.to< ExecutionConfiguration >();

		if( aConf.getCode().is< Operator >() )
		{
			if( aConf.getCode().to< Operator >().
					isOpCode( AVM_OPCODE_RUN ) )
			{
				RuntimeID aRID = aConf.getRuntimeID();
				while( aRID.valid() && (aRID.getInstance() != aTP.object) )
				{
					aRID = aRID.getPRID();
				}
				return( aRID.valid() );
			}
		}
	}
	else if( aTrace.is< AvmCode >() )
	{
		for( const auto & itOperand : aTrace.to< AvmCode >().getOperands() )
		{
			if( isSatMachine(anEC, aTP, itOperand) )
			{
				return( true );
			}
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// WILL NEVER SAT CHECKING API
////////////////////////////////////////////////////////////////////////////////

bool TraceChecker::willNeverSat(const ExecutionContext & anEC, const BF & arg)
{
	if( anEC.isRoot() )
	{
		return( false );
	}

	if( arg.is< TracePoint >() )
	{
		if( willNeverSat(anEC, arg.to_ptr< TracePoint >()) )
		{
			return( true );
		}
	}
	else if( arg.is< AvmCode >() )
	{
		return( willNeverSat(anEC, arg.to_ptr< AvmCode >()) );
	}

	return( false );
}


bool TraceChecker::willNeverSat(const ExecutionContext & anEC, AvmCode * aCode)
{
	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_AND:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_AND_THEN:
		{
			for( const auto & itOperand : aCode->getOperands() )
			{
				if( not willNeverSat(anEC, itOperand) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			for( const auto & itOperand : aCode->getOperands() )
			{
				if( willNeverSat(anEC, itOperand) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_XOR:
		{
			std::size_t passCount = 0;

			for( const auto & itOperand : aCode->getOperands() )
			{
				if( willNeverSat(anEC, itOperand) )
				{
					if( ++passCount > 1 )
					{
						return( false );
					}
				}
			}

			return( passCount == 1 );
		}


		case AVM_OPCODE_NOT:
		{
			return( not willNeverSat(anEC, aCode->first()) );
		}


		case AVM_OPCODE_NAND:
		{
			for( const auto & itOperand : aCode->getOperands() )
			{
				if( not willNeverSat(anEC, itOperand) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_NOR:
		{
			for( const auto & itOperand : aCode->getOperands() )
			{
				if( willNeverSat(anEC, itOperand) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_XNOR:
		{
			std::size_t passCount = 0;

			for( const auto & itOperand : aCode->getOperands() )
			{
				if( willNeverSat(anEC, itOperand) )
				{
					if( ++passCount > 1 )
					{
						return( true );
					}
				}
			}

			return( passCount != 1 );
		}

		default:
		{
			return( false );
		}
	}
}


bool TraceChecker::willNeverSat(
		const ExecutionContext & anEC, AVM_OPCODE anOp, const BF & arg)
{
	switch( anOp )
	{
		case AVM_OPCODE_AND:
		case AVM_OPCODE_STRONG_SYNCHRONOUS:
		case AVM_OPCODE_AND_THEN:
		case AVM_OPCODE_SCHEDULE_AND_THEN:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( not willNeverSat(anEC, argArray->at(offset)) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_OR:
		case AVM_OPCODE_OR_ELSE:
		case AVM_OPCODE_SCHEDULE_OR_ELSE:
		case AVM_OPCODE_WEAK_SYNCHRONOUS:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( willNeverSat(anEC, argArray->at(offset)) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_XOR:
		case AVM_OPCODE_EXCLUSIVE:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			std::size_t passCount = 0;

			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( willNeverSat(anEC, argArray->at(offset)) )
				{
					if( ++passCount > 1 )
					{
						return( false );
					}
				}
			}

			return( passCount == 1 );
		}


		case AVM_OPCODE_NOT:
		{
			return( not willNeverSat(anEC, arg) );
		}


		case AVM_OPCODE_NAND:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( not willNeverSat(anEC, argArray->at(offset)) )
				{
					return( true );
				}
			}

			return( false );
		}

		case AVM_OPCODE_NOR:
		{
			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( willNeverSat(anEC, argArray->at(offset)) )
				{
					return( false );
				}
			}

			return( true );
		}

		case AVM_OPCODE_XNOR:
		{
			std::size_t passCount = 0;

			ArrayBF * argArray = arg.to_ptr< ArrayBF >();
			std::size_t endOffset = argArray->size();
			for( std::size_t offset = 0 ; offset < endOffset ; ++offset )
			{
				if( willNeverSat(anEC, argArray->at(offset)) )
				{
					if( ++passCount > 1 )
					{
						return( true );
					}
				}
			}

			return( passCount != 1 );
		}

		default:
		{
			return( false );
		}
	}
}


bool TraceChecker::willNeverSat(const ExecutionContext & anEC, const TracePoint & aTP)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , SOLVING )
	AVM_OS_TRACE << "willNeverSat ? EC:> " << anEC.str_min() << std::endl
			<< "run#trace:> " << anEC.getRunnableElementTrace().str() << std::endl
			<< "io#race  :> " << anEC.getIOElementTrace().str() << std::endl;
	AVM_OS_TRACE << "Point:>" << str_indent( aTP ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , SOLVING )


	switch( aTP.nature )
	{
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE_LEAF:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE_LEAF:

		case ENUM_TRACE_POINT::TRACE_FORMULA_NATURE:
		case ENUM_TRACE_POINT::TRACE_CONDITION_NATURE:
		case ENUM_TRACE_POINT::TRACE_DECISION_NATURE:

		case ENUM_TRACE_POINT::TRACE_TIME_NATURE:
		case ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE:
		case ENUM_TRACE_POINT::TRACE_COM_NATURE:
		case ENUM_TRACE_POINT::TRACE_PORT_NATURE:
		case ENUM_TRACE_POINT::TRACE_SIGNAL_NATURE:
		case ENUM_TRACE_POINT::TRACE_MESSAGE_NATURE:
		case ENUM_TRACE_POINT::TRACE_CHANNEL_NATURE:
		{
			return( false );
		}


		case ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE:
		{
			return( willNeverSatTransition(anEC, aTP) );
		}

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		{
			return( willNeverSatState(anEC, aTP) );
		}

		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		{
			return( willNeverSatStatemachine(anEC, aTP) );
		}

		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			return( willNeverSatMachine(anEC, aTP) );
		}

		case ENUM_TRACE_POINT::TRACE_COMPOSITE_NATURE:
		{
			return( willNeverSat(anEC, aTP.op, aTP.value) );
		}

		default:
		{
			return( false );
		}
	}
}


bool TraceChecker::willNeverSatTransition(
		const ExecutionContext & anEC, const TracePoint & aTP)
{
	ExecutableForm * sourceExecutable =
			aTP.object->as_ptr< AvmTransition >()->getExecutableContainer();

	if( not sourceExecutable->hasPossibleDynamicInstanciation() )
	{
		return( false );
	}

	TableOfRuntimeT::const_iterator itRF =
			anEC.getExecutionData().getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF =
			anEC.getExecutionData().getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != endRF ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( anEC.getExecutionData().isIdleOrRunning(itRID) &&
				itRID.refExecutable().hasForwardReachableMachine() )
		{
			if( (sourceExecutable == itRID.getExecutable()) ||
				sourceExecutable->getBackwardReachableMachine().
						contains(itRID.getInstance()) )
			{
				return( false );
			}
		}
	}

	return( true );
}

bool TraceChecker::willNeverSatState(
		const ExecutionContext & anEC, const TracePoint & aTP)
{
	ExecutableForm * sourceExecutable =
			aTP.object->as_ptr< InstanceOfMachine >()->getExecutable();

	if( not sourceExecutable->hasSingleRuntimeInstance() )
	{
		return( false );
	}

	TableOfRuntimeT::const_iterator itRF =
			anEC.getExecutionData().getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF =
			anEC.getExecutionData().getTableOfRuntime().end();
	for( RuntimeID itRID ; itRF != endRF ; ++itRF )
	{
		itRID = (*itRF)->getRID();

		if( anEC.getExecutionData().isIdleOrRunning(itRID) &&
				itRID.refExecutable().hasForwardReachableMachine() )
		{
			if( (sourceExecutable == itRID.getExecutable()) ||
				sourceExecutable->getBackwardReachableMachine().
						contains(itRID.getInstance()) )
			{
				return( false );
			}
		}
	}

	return( false );
}


bool TraceChecker::willNeverSatStatemachine(
		const ExecutionContext & anEC, const TracePoint & aTP)
{
	return( willNeverSatState(anEC, aTP) );
}


bool TraceChecker::willNeverSatMachine(
		const ExecutionContext & anEC, const TracePoint & aTP)
{
	return( willNeverSatState(anEC, aTP) );
}


} /* namespace sep */
