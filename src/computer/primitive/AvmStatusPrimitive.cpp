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

#include "AvmStatusPrimitive.h"

#include <common/BF.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/ExpressionComparer.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/operator/Operator.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// COMPUTE STATUS STATE
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

static bool firedTraceIsRun(const BF & aFiredTrace, const RuntimeID & aRID)
{
	if( aFiredTrace.invalid() )
	{
		return false;
	}

	switch( aFiredTrace.classKind() )
	{
		case FORM_AVMCODE_KIND:
		{
			const AvmCode & anAvmCode = aFiredTrace.to< AvmCode >();

			for( const auto & itOperand : anAvmCode.getOperands() )
			{
				if( firedTraceIsRun(itOperand, aRID) )
				{
					return( true );
				}
			}

			break;
		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			const ExecutionConfiguration & anExecConf =
					aFiredTrace.to< ExecutionConfiguration >();

			if( aRID == anExecConf.getRuntimeID() )
			{
				return( anExecConf.getOperator().isOpCode( AVM_OPCODE_RUN ) );
			}
			break;
		}

		case FORM_EXECUTION_CONTEXT_KIND:
		{
			return( firedTraceIsRun( aFiredTrace.to<
					ExecutionContext >().getRunnableElementTrace(), aRID) );
		}

		default:
		{
			break;
		}
	}

	return( false );
}


static bool firedTraceIsRun(const ExecutionData & anED, const RuntimeID & aRID)
{
	return( firedTraceIsRun(anED.getRunnableElementTrace(), aRID)
			|| firedTraceIsRun(anED.getExecutionContext()->
					getRunnableElementTrace(), aRID) );
}



static bool computeStatusStateIs(const ExecutionData & apED,
		const RuntimeID & aRID, const AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_RUN:
		{
			return( apED.isRunning(aRID) || firedTraceIsRun(apED, aRID) );
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			return( apED.isIdle(aRID) );
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			return(    apED.isDefinedPES(aRID) &&
					(! apED.isLoaded(aRID))    &&
					(! apED.isStarting(aRID))  &&
					(! apED.isFinalized(aRID)) &&
					(! apED.isDestroyed(aRID))
			);
		}


		case AVM_OPCODE_ENABLE_INVOKE:
		{
			return( apED.isIdleOrRunning(aRID) );
		}

		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		{
			return( apED.isDisableOrAborted(aRID) );
		}


		case AVM_OPCODE_FINAL:
		{
			return( apED.isFinalized(aRID) );
		}

		case AVM_OPCODE_DESTROY:
		{
			return( apED.isDestroyed(aRID) );
		}


		case AVM_OPCODE_SUSPEND:
		{
			return( apED.isSuspended(aRID) );
		}

		case AVM_OPCODE_STOP:
		{
			return( apED.isStopped(aRID) );
		}


		case AVM_OPCODE_WAIT:
		{
			return( apED.isWaiting(aRID) );
		}


		default:
		{
			return( false );
		}
	}
}



static bool computeStatusBeing(const ExecutionData & prevED,
		const ExecutionData & anED, const RuntimeID & aRID, AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_RUN:
		{
			if( prevED.valid() )
			{
				return( (! firedTraceIsRun(prevED, aRID) ) &&
						(anED.isRunning(aRID) || firedTraceIsRun(anED, aRID)) );
			}
			else
			{
				return( anED.isRunning(aRID) );
			}
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( (! prevED.isIdle(aRID)) && anED.isIdle(aRID) );
			}
			else
			{
				return( anED.isRunning(aRID) );
			}
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			if( prevED.valid() )
			{
				return( (! prevED.isStarting(aRID)) &&
						anED.isStarting(aRID) );
			}
			else
			{
				return( anED.isStarting(aRID) );
			}
		}

		case AVM_OPCODE_FINAL:
		{
			if( prevED.valid() )
			{
				return( (! prevED.isFinalizing(aRID)) &&
						anED.isFinalizing(aRID) );
			}
			else
			{
				return( anED.isFinalizing(aRID) );
			}
		}

		case AVM_OPCODE_ENABLE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED.isDisableOrAborted(aRID) &&
						anED.isIdleOrRunning(aRID) );
			}
			else
			{
				return( anED.isIdleOrRunning(aRID) );
			}
		}

		case AVM_OPCODE_DISABLE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED.isIdleOrRunning(aRID) &&
						anED.isDisable(aRID) );
			}
			else
			{
				return( anED.isIdleOrRunning(aRID) );
			}
		}

		case AVM_OPCODE_ABORT_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED.isIdleOrRunning(aRID)
						&& anED.isAborted(aRID) );
			}
			else
			{
				return( anED.isIdleOrRunning(aRID) );
			}
		}


		case AVM_OPCODE_SUSPEND:
		{
			if( prevED.valid() )
			{
				return( (! prevED.isSuspended(aRID))
						&& anED.isSuspended(aRID) );
			}
			else
			{
				return( anED.isSuspended(aRID) );
			}
		}


		case AVM_OPCODE_WAIT:
		{
			if( prevED.valid() )
			{
				return( (! prevED.isWaiting(aRID))
						&& anED.isWaiting(aRID) );
			}
			else
			{
				return( anED.isWaiting(aRID) );
			}
		}


		default:
		{
			return( false );
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// STATUS WAS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_StatusWas::seval(EvaluationEnvironment & ENV)
{
	if( ENV.inEC->hasPrevious() )
	{
		const Operator & anOperator = ENV.mARG->at(0).to< Operator >();

		switch( anOperator.getAvmOpCode() )
		{
			case AVM_OPCODE_ASSIGN:
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						ENV.isAssigned(ENV.mARG->outED.getPrevious(),
								ENV.mARG->outED.getRID(),
								ENV.mARG->at(1).to< InstanceOfData >()));
				return( true );
			}

			default:
			{
				const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

				if( aRID.valid() )
				{
					ENV.outVAL = ExpressionConstructor::newBoolean(
							computeStatusStateIs(ENV.mARG->outED.getPrevious(),
									aRID, anOperator.getAvmOpCode()));
					return( true );
				}
				else
				{
					return( false );
				}
			}
		}
	}
	else
	{
		ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;

		return( true );
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// STATUS IS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_StatusIs::seval(EvaluationEnvironment & ENV)
{
	const Operator & anOperator = ENV.mARG->at(0).to< Operator >();

	switch( anOperator.getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		{
			ENV.outVAL = ExpressionConstructor::newBoolean(
					ENV.isAssigned(ENV.mARG->outED,
							ENV.mARG->outED.getRID(),
							ENV.mARG->at(1).to< InstanceOfData >()) );
			return( true );
		}

		default:
		{
			const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

			if( aRID.valid() )
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						computeStatusStateIs(ENV.mARG->outED, aRID,
								anOperator.getAvmOpCode()));
				return( true );
			}
			else
			{
				return( false );
			}
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// STATUS BEING
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_StatusBeing::seval(EvaluationEnvironment & ENV)
{
	if( ENV.inEC->hasPrevious() )
	{
		const Operator & anOperator = ENV.mARG->at(0).to< Operator >();

		switch( anOperator.getAvmOpCode() )
		{
			case AVM_OPCODE_ASSIGN:
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						ENV.isAssigned(ENV.mARG->outED,
								ENV.mARG->outED.getRID(),
								ENV.mARG->at(1).to< InstanceOfData >()) );
				return( true );
			}

			default:
			{
				const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

				if( aRID.valid() )
				{
					ENV.outVAL = ExpressionConstructor::newBoolean(
							computeStatusBeing(ENV.mARG->outED.getPrevious(),
									ENV.mARG->outED, aRID,
									anOperator.getAvmOpCode()));
					return( true );
				}
				else
				{
					return( false );
				}
			}
		}
	}
	else
	{
		ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// STATUS WILL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


bool AvmPrimitive_StatusWill::seval(EvaluationEnvironment & ENV)
{
	const Operator & anOperator = ENV.mARG->at(0).to< Operator >();

	bool evalStatusFlag = false;

	switch( anOperator.getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		{
			const InstanceOfData & lvalue =
					ENV.mARG->at(1).to< InstanceOfData >();

			evalStatusFlag = false;
			for( const auto & itChildEC : ENV.inEC->getChildContexts() )
			{
				if( ENV.isAssigned(itChildEC->getExecutionData(),
						ENV.mARG->outED.getRID(), lvalue) )
				{
					evalStatusFlag = true;
					break;
				}
			}

			ENV.outVAL = ExpressionConstructor::newBoolean(evalStatusFlag);

			return( true );
		}

		default:
		{
			const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

			if( aRID.valid() )
			{
				for( const auto & itChildEC : ENV.inEC->getChildContexts() )
				{
					if( computeStatusStateIs(itChildEC->getExecutionData(),
							aRID, anOperator.getAvmOpCode()) )
					{
						evalStatusFlag = true;
						break;
					}
				}
				ENV.outVAL = ExpressionConstructor::newBoolean(evalStatusFlag);
				return( true );
			}
			else
			{
				return( false );
			}
		}
	}
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// CHANGED
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_Changed::seval(EvaluationEnvironment & ENV)
{
	const InstanceOfData & lvalue = ENV.mARG->at(0).to< InstanceOfData >();

	bool isChangedFlag = true;

	if( ENV.isAssigned(ENV.mARG->outED, ENV.mARG->outED.getRID(), lvalue) )
	{
		isChangedFlag = true;
		const BF & currentValue = ENV.getRvalue(ENV.mARG->outED,
				ENV.mARG->outED.getRID(), lvalue);

		if( ENV.inEC->hasPrevious() )
		{
			isChangedFlag = currentValue.strNEQ(
					ENV.getRvalue(ENV.mARG->outED.getPrevious(),
							ENV.mARG->outED.getRID(), lvalue));
		}

		if( (! isChangedFlag) && ENV.mARG->outED.hasExecutionContext() &&
				ENV.mARG->outED.getExecutionContext()->
						getExecutionData().isTNEQ( ENV.mARG->outED ) )
		{
			isChangedFlag = currentValue.strNEQ( ENV.getRvalue(
					ENV.mARG->outED.getExecutionContext()->getwExecutionData(),
					ENV.mARG->outED.getRID(), lvalue) );
		}
		else
		{
			isChangedFlag = false;
		}
	}
	else
	{
		isChangedFlag = false;
	}

	ENV.outVAL = ExpressionConstructor::newBoolean( isChangedFlag );

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// CHANGED TO
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

//!! TODO OPTIMIZATION
bool AvmPrimitive_ChangedTo::seval(EvaluationEnvironment & ENV)
{
	const InstanceOfData & lvalue = ENV.mARG->at(0).to< InstanceOfData >();

	if( ENV.isAssigned(ENV.mARG->outED, ENV.mARG->outED.getRID(), lvalue) )
	{
		const BF & currentValue = ENV.getRvalue(ENV.mARG->outED,
				ENV.mARG->outED.getRID(), lvalue);

		ENV.outVAL = ExpressionConstructor::newBoolean(
				currentValue.strNEQ( ENV.mARG->at(1) ) );
	}
	else
	{
		ENV.outVAL = ExpressionConstant::BOOLEAN_FALSE;
	}

	return( true );
}



}
