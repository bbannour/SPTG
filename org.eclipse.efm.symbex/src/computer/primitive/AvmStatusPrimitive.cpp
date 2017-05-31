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
			const AvmCode * anAvmCode = aFiredTrace.to_ptr< AvmCode >();

			AvmCode::const_iterator it = anAvmCode->begin();
			AvmCode::const_iterator itEnd = anAvmCode->end();
			for( ; it != itEnd ; ++it )
			{
				if( firedTraceIsRun((*it), aRID) )
				{
					return( true );
				}
			}

			break;
		}

		case FORM_EXECUTION_CONFIGURATION_KIND:
		{
			const ExecutionConfiguration * anExecConf =
					aFiredTrace.to_ptr< ExecutionConfiguration >();

			if( aRID == anExecConf->getRuntimeID() )
			{
				return( anExecConf->getOperator()->
						isOpCode( AVM_OPCODE_RUN ) );
			}
			break;
		}

		case FORM_EXECUTION_CONTEXT_KIND:
		{
			return( firedTraceIsRun( aFiredTrace.to_ptr<
					ExecutionContext >()->getRunnableElementTrace(), aRID) );
		}

		case FORM_EXECUTION_DATA_KIND:
		{
			return( firedTraceIsRun(aFiredTrace.to_ptr<
						ExecutionData >()->getRunnableElementTrace(), aRID)
				|| firedTraceIsRun(aFiredTrace.to_ptr< ExecutionData >()->
						getExecutionContext()->getRunnableElementTrace(), aRID) );
		}

		default:
		{
			break;
		}
	}

	return( false );
}



static bool computeStatusStateIs(const APExecutionData & apED,
		const RuntimeID & aRID, const AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_RUN:
		{
			return( apED->isRunning(aRID) || firedTraceIsRun(apED, aRID) );
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			return( apED->isIdle(aRID) );
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			return(    apED->isDefinedPES(aRID) &&
					(! apED->isLoaded(aRID))    &&
					(! apED->isStarting(aRID))  &&
					(! apED->isFinalized(aRID)) &&
					(! apED->isDestroyed(aRID))
			);
		}


		case AVM_OPCODE_ENABLE_INVOKE:
		{
			return( apED->isIdleOrRunning(aRID) );
		}

		case AVM_OPCODE_DISABLE_INVOKE:
		case AVM_OPCODE_ABORT_INVOKE:
		{
			return( apED->isDisableOrAborted(aRID) );
		}


		case AVM_OPCODE_FINAL:
		{
			return( apED->isFinalized(aRID) );
		}

		case AVM_OPCODE_DESTROY:
		{
			return( apED->isDestroyed(aRID) );
		}


		case AVM_OPCODE_SUSPEND:
		{
			return( apED->isSuspended(aRID) );
		}

		case AVM_OPCODE_STOP:
		{
			return( apED->isStopped(aRID) );
		}


		case AVM_OPCODE_WAIT:
		{
			return( apED->isWaiting(aRID) );
		}


		default:
		{
			return( false );
		}
	}
}



static bool computeStatusBeing(const APExecutionData & prevED,
		const APExecutionData & anED, const RuntimeID & aRID, AVM_OPCODE op)
{
	switch( op )
	{
		case AVM_OPCODE_RUN:
		{
			if( prevED.valid() )
			{
				return( (! firedTraceIsRun(prevED, aRID) ) &&
						(anED->isRunning(aRID) || firedTraceIsRun(anED, aRID)) );
			}
			else
			{
				return( anED->isRunning(aRID) );
			}
		}

		case AVM_OPCODE_SCHEDULE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( (! prevED->isIdle(aRID)) && anED->isIdle(aRID) );
			}
			else
			{
				return( anED->isRunning(aRID) );
			}
		}

		case AVM_OPCODE_START:
		case AVM_OPCODE_RESTART:
		{
			if( prevED.valid() )
			{
				return( (! prevED->isStarting(aRID)) &&
						anED->isStarting(aRID) );
			}
			else
			{
				return( anED->isStarting(aRID) );
			}
		}

		case AVM_OPCODE_FINAL:
		{
			if( prevED.valid() )
			{
				return( (! prevED->isFinalizing(aRID)) &&
						anED->isFinalizing(aRID) );
			}
			else
			{
				return( anED->isFinalizing(aRID) );
			}
		}

		case AVM_OPCODE_ENABLE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED->isDisableOrAborted(aRID) &&
						anED->isIdleOrRunning(aRID) );
			}
			else
			{
				return( anED->isIdleOrRunning(aRID) );
			}
		}

		case AVM_OPCODE_DISABLE_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED->isIdleOrRunning(aRID) &&
						anED->isDisable(aRID) );
			}
			else
			{
				return( anED->isIdleOrRunning(aRID) );
			}
		}

		case AVM_OPCODE_ABORT_INVOKE:
		{
			if( prevED.valid() )
			{
				return( prevED->isIdleOrRunning(aRID) &&
						anED->isAborted(aRID) );
			}
			else
			{
				return( anED->isIdleOrRunning(aRID) );
			}
		}


		case AVM_OPCODE_SUSPEND:
		{
			if( prevED.valid() )
			{
				return( (! prevED->isSuspended(aRID)) &&
						anED->isSuspended(aRID) );
			}
			else
			{
				return( anED->isSuspended(aRID) );
			}
		}


		case AVM_OPCODE_WAIT:
		{
			if( prevED.valid() )
			{
				return( (! prevED->isWaiting(aRID)) &&
						anED->isWaiting(aRID) );
			}
			else
			{
				return( anED->isWaiting(aRID) );
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
		Operator * anOperator = ENV.mARG->at(0).to_ptr< Operator >();

		switch( anOperator->getAvmOpCode() )
		{
			case AVM_OPCODE_ASSIGN:
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						ENV.isAssigned(ENV.mARG->outED.getPrevious(),
								ENV.mARG->outED->mRID,
								ENV.mARG->at(1).to_ptr< InstanceOfData >()));
				return( true );
			}

			default:
			{
				const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

				if( aRID.valid() )
				{
					ENV.outVAL = ExpressionConstructor::newBoolean(
							computeStatusStateIs(ENV.mARG->outED.getPrevious(),
									aRID, anOperator->getAvmOpCode()));
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
	Operator * anOperator = ENV.mARG->at(0).to_ptr< Operator >();

	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		{
			ENV.outVAL = ExpressionConstructor::newBoolean(
					ENV.isAssigned(ENV.mARG->outED,
							ENV.mARG->outED->mRID,
							ENV.mARG->at(1).to_ptr< InstanceOfData >()) );
			return( true );
		}

		default:
		{
			const RuntimeID & aRID = ENV.mARG->at(1).bfRID();

			if( aRID.valid() )
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						computeStatusStateIs(ENV.mARG->outED, aRID,
								anOperator->getAvmOpCode()));
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
		Operator * anOperator = ENV.mARG->at(0).to_ptr< Operator >();

		switch( anOperator->getAvmOpCode() )
		{
			case AVM_OPCODE_ASSIGN:
			{
				ENV.outVAL = ExpressionConstructor::newBoolean(
						ENV.isAssigned(ENV.mARG->outED,
								ENV.mARG->outED->mRID,
								ENV.mARG->at(1).to_ptr< InstanceOfData >()) );
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
									anOperator->getAvmOpCode()));
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
	Operator * anOperator = ENV.mARG->at(0).to_ptr< Operator >();

	bool evalStatusFlag = false;

	switch( anOperator->getAvmOpCode() )
	{
		case AVM_OPCODE_ASSIGN:
		{
			InstanceOfData * lvalue = ENV.mARG->at(1).to_ptr< InstanceOfData >();

			ExecutionContext::child_iterator endEC = ENV.inEC->end();
			ExecutionContext::child_iterator itEC;

			evalStatusFlag = false;
			for( itEC = ENV.inEC->begin() ; itEC != endEC ; ++itEC )
			{
				if( ENV.isAssigned((*itEC)->getAPExecutionData(),
						ENV.mARG->outED->mRID, lvalue) )
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
				ExecutionContext::child_iterator endEC = ENV.inEC->end();
				ExecutionContext::child_iterator itEC;

				for( itEC = ENV.inEC->begin() ; itEC != endEC ; ++itEC )
				{
					if( computeStatusStateIs((*itEC)->getAPExecutionData(),
							aRID, anOperator->getAvmOpCode()) )
					{
						evalStatusFlag = true;
						break;
					}
				}
				ENV.outVAL =
						ExpressionConstructor::newBoolean(
								evalStatusFlag);
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
	InstanceOfData * lvalue = ENV.mARG->at(0).to_ptr< InstanceOfData >();

	bool isChangedFlag = true;

	if( ENV.isAssigned(ENV.mARG->outED, ENV.mARG->outED->mRID, lvalue) )
	{
		isChangedFlag = true;
		const BF & currentValue = ENV.getRvalue(ENV.mARG->outED,
				ENV.mARG->outED->mRID, lvalue);

		if( ENV.inEC->hasPrevious() )
		{
			isChangedFlag = currentValue.strNEQ(
					ENV.getRvalue(ENV.mARG->outED.getPrevious(),
							ENV.mARG->outED->mRID, lvalue));
		}

		if( (! isChangedFlag) && ENV.mARG->outED->hasExecutionContext() &&
				(ENV.mARG->outED->getExecutionContext()->
						getAPExecutionData() != ENV.mARG->outED) )
		{
			isChangedFlag = currentValue.strNEQ(
					ENV.getRvalue(ENV.mARG->outED->getExecutionContext()->
						getAPExecutionData(), ENV.mARG->outED->mRID, lvalue));
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
	InstanceOfData * lvalue = ENV.mARG->at(0).to_ptr< InstanceOfData >();

	if( ENV.isAssigned(ENV.mARG->outED, ENV.mARG->outED->mRID, lvalue) )
	{
		const BF & currentValue = ENV.getRvalue(ENV.mARG->outED,
				ENV.mARG->outED->mRID, lvalue);

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
