/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceFilter.h"

#include <computer/EvaluationEnvironment.h>

#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/expression/BuiltinArray.h>

#include <fml/operator/OperatorManager.h>

#include <fml/template/TimedMachine.h>

#include <fml/runtime/ExecutionConfiguration.h>

#include <fml/trace/TraceFactory.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{

/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 ...
 section TRACE
  // AND --> conjunctive
  // OR  --> disjunctive
  // XOR --> exclusive
  // NOT --> negative
  @combinator = 'OR';

  @time = "$delta";
  @time = "$time";

  @assign = "sens";

  @newfresh = "sens";

  @signal = "sens";

  @port = "env";

  @input = "env";
  @output = "env";

  @output = "Thermostat->dt";
  @input  = "Thermostat->equip";
  @output = "Equipment->error";
 endsection TRACE
 ...
endprototype
*/

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

#define LEAF_NODE_REGEX_PATTERN     "\\S?(leaf|end|last|tail)\\S?"

#define LEAF_NODE_DEFAULT_PATTERN   ":leaf:"


bool TraceFilter::configure(EvaluationEnvironment & ENV,
		WObject * wfParameterObject, WObject * wfTraceObject)
{

	if( TimedMachine::SYSTEM_VAR_DELTA_TIME != NULL )
	{
		ExecutableQuery XQuery( ENV.getConfiguration() );

		objectDeltaTime = XQuery.getDataByAstElement(
			TimedMachine::SYSTEM_VAR_DELTA_TIME).to_ptr< InstanceOfData >();
	}

	// default main combinator
	mainTracePointFiter.setOperator( OperatorManager::OPERATOR_OR );

	// Configuration of TRACE
	TraceFactory traceFactory(ENV.getConfiguration(),
			ENV, wfParameterObject, NULL, objectDeltaTime);
	if( not traceFactory.configure(wfTraceObject, (& mainTracePointFiter)) )
	{
//		return( false );
	}

	listOfVariableTracePoint.append( traceFactory.getVariableTracePoints() );


	// Initialize Filter Point Flags
	mConditionFlag = Query::hasRegexWProperty(wfTraceObject, "condition");
	mDecisionFlag = mConditionFlag
			|| Query::hasRegexWProperty(wfTraceObject, "decision");

	if(  mConditionFlag || mDecisionFlag  )
	{
		mPathConditionFlag = mPathTimedConditionFlag = true;
		mNodeConditionFlag = mNodeTimedConditionFlag = true;

		mPathConditionLeafNodeFlag = mPathTimedConditionLeafNodeFlag = true;
		mNodeConditionLeafNodeFlag = mNodeTimedConditionLeafNodeFlag = true;
	}
	else
	{
		mPathConditionFlag = not REGEX_MATCH(
				Query::getRegexWPropertyString(wfTraceObject,
					CONS_WID2("path", "condition"), LEAF_NODE_DEFAULT_PATTERN),
				LEAF_NODE_REGEX_PATTERN );

		mPathConditionLeafNodeFlag = mPathConditionFlag
				|| Query::hasRegexWProperty(wfTraceObject,
					CONS_WID3("path", "condition", "(leaf|end|last|tail)"))
				|| REGEX_MATCH(Query::getRegexWPropertyString(
							wfTraceObject, CONS_WID2("path", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );


		mNodeConditionFlag = not REGEX_MATCH(
				Query::getRegexWPropertyString(wfTraceObject,
					CONS_WID2("node", "condition"), LEAF_NODE_DEFAULT_PATTERN),
				LEAF_NODE_REGEX_PATTERN );

		mNodeConditionLeafNodeFlag = mNodeConditionFlag
				|| Query::hasRegexWProperty(wfTraceObject,
					CONS_WID3("node", "condition", "(leaf|end|last|tail)"))
				|| REGEX_MATCH(Query::getRegexWPropertyString(
							wfTraceObject, CONS_WID2("node", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );


		mPathTimedConditionFlag = not REGEX_MATCH(
				Query::getRegexWPropertyString(wfTraceObject,
					CONS_WID3("path", "timed", "condition"),
					LEAF_NODE_DEFAULT_PATTERN),
				LEAF_NODE_REGEX_PATTERN );

		mPathTimedConditionLeafNodeFlag = mPathTimedConditionFlag
				|| Query::hasRegexWProperty(wfTraceObject, CONS_WID4(
						"path", "timed", "condition", "(leaf|end|last|tail)") )
				|| REGEX_MATCH(Query::getRegexWPropertyString(wfTraceObject,
						CONS_WID3("path", "timed", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );


		mNodeTimedConditionFlag = not REGEX_MATCH(
				Query::getRegexWPropertyString(wfTraceObject,
					CONS_WID3("node", "timed", "condition"),
					LEAF_NODE_DEFAULT_PATTERN),
				LEAF_NODE_REGEX_PATTERN );

		mNodeTimedConditionLeafNodeFlag = mNodeTimedConditionFlag
				|| Query::hasRegexWProperty(wfTraceObject, CONS_WID4(
						"node", "timed", "condition", "(leaf|end|last|tail)") )
				|| REGEX_MATCH(Query::getRegexWPropertyString(wfTraceObject,
						CONS_WID3("node", "timed", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );
	}

	mTimeFilterFlag = Query::hasRegexWProperty(wfTraceObject, "\\S?time");

	mAssignFilterFlag = listOfVariableTracePoint.nonempty()
			|| Query::hasWPropertyString(wfTraceObject, "variable", "var")
			|| Query::hasWPropertyString(wfTraceObject, "assign"  );

	mNewfreshFilterFlag = Query::hasWPropertyString(wfTraceObject, "newfresh");

	mComFilterFlag = Query::hasRegexWProperty(wfTraceObject, "com|inout");

	if( mComFilterFlag )
	{
		mInputFilterFlag  = true;
		mInputExternalFilterFlag  = mInputEnvFilterFlag  = true;
		mInputInternalFilterFlag  = mInputRdvFilterFlag  = true;

		mOutputFilterFlag = true;
		mOutputExternalFilterFlag = mOutputEnvFilterFlag = true;
		mOutputInternalFilterFlag = mOutputRdvFilterFlag = true;
	}
	else
	{
		mInputEnvFilterFlag =
				Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("((in(p|o)ut)|com)", "env"));
		mInputRdvFilterFlag =
				Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("((in(p|o)ut)|com)", "rdv"));

		mInputExternalFilterFlag = mInputEnvFilterFlag
				|| Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("((in(p|o)ut)|com)", "external"));

		mInputInternalFilterFlag = mInputRdvFilterFlag
				|| Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("((in(p|o)ut)|com)", "internal"));

		mInputFilterFlag = mInputExternalFilterFlag
				|| mInputInternalFilterFlag
				|| Query::hasWPropertyString(wfTraceObject, "input");


		mOutputEnvFilterFlag = Query::hasRegexWProperty(
				wfTraceObject, CONS_WID2("output", "env"));

		mOutputRdvFilterFlag = Query::hasRegexWProperty(
				wfTraceObject, CONS_WID2("output", "rdv"));

		mOutputExternalFilterFlag = mOutputEnvFilterFlag
				|| Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("(((outp|ino)ut)|com)", "external"));

		mOutputInternalFilterFlag = mOutputRdvFilterFlag
				|| Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("(((outp|ino)ut)|com)", "internal"));

		mOutputFilterFlag =
				mOutputExternalFilterFlag || mOutputInternalFilterFlag
				|| Query::hasWPropertyString(wfTraceObject, "output");


		mComExternalFilterFlag =
				mInputExternalFilterFlag || mOutputExternalFilterFlag
				|| Query::hasRegexWProperty(
						wfTraceObject, CONS_WID2("(com|inout)", "external"));

		mComInternalFilterFlag =
				mInputInternalFilterFlag || mOutputInternalFilterFlag
				|| Query::hasRegexWProperty(wfTraceObject,
						CONS_WID2("(com|inout)", "internal"));

		mComFilterFlag = mInputFilterFlag || mOutputFilterFlag || containsCom();
	}

	mMachineFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "machine");
	mStateFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "state");
	mStatemachineFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "statemachine");

	mTransitionFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "transition");
	mRoutineFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "routine");

	mIOTraceFilterFlag = mComFilterFlag || mNewfreshFilterFlag;

	mRunnableFilterFlag = mMachineFilterFlag
			|| mStateFilterFlag      || mStatemachineFilterFlag
			|| mTransitionFilterFlag || mRoutineFilterFlag;


	// Update Filter Point Flags
	//updateFilterFlags();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_TRACE << "TraceFilter:> "; toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	return( true );
}


bool TraceFilter::configure(EvaluationEnvironment & ENV,
		WObject * wfParameterObject, const std::string & aWSequenceNameID,
		const std::string & aWSequenceElseNameID)
{
	WObject * theTRACE = Query::getWSequenceOrElse(
			wfParameterObject, aWSequenceNameID, aWSequenceElseNameID);

//	if( (theTRACE == WObject::_NULL_) || theTRACE->hasnoOwnedElement() )
//	{
//		return( true );
//	}

	return( configure(ENV, wfParameterObject, theTRACE) );
}

/**
 * Update
 * Filter Point Flags
 */
//void TraceFilter::updateFilterFlags()
//{
//	mPathConditionFlag = contains(
//			ENUM_TRACE_POINT::TRACE_PATH_CONDITION_NATURE);
//
//	mPathTimedConditionFlag = contains(
//			ENUM_TRACE_POINT::TRACE_PATH_TIMED_CONDITION_NATURE);
//
//	mNodeConditionFlag = contains(
//			ENUM_TRACE_POINT::TRACE_NODE_CONDITION_NATURE);
//
//	mNodeTimedConditionFlag = contains(
//			ENUM_TRACE_POINT::TRACE_NODE_TIMED_CONDITION_NATURE);
//
//	mTimeFilterFlag = contains(ENUM_TRACE_POINT::TRACE_TIME_NATURE);
//
//	mTimeFilterFlag = contains(ENUM_TRACE_POINT::TRACE_TIME_NATURE);
//
//	mAssignFilterFlag = listOfVariableTracePoint.nonempty() ||
//			contains(ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE);
//
//	mNewfreshFilterFlag = contains(ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
//			AVM_OPCODE_ASSIGN_NEWFRESH);
//
//	mInputEnvFilterFlag = contains(AVM_OPCODE_INPUT_ENV);
//	mInputFilterFlag = contains(AVM_OPCODE_INPUT);
//	mOutputEnvFilterFlag = contains(AVM_OPCODE_OUTPUT_ENV);
//	mOutputFilterFlag = contains(AVM_OPCODE_OUTPUT);
//
//	mMachineFilterFlag = contains(ENUM_TRACE_POINT::TRACE_MACHINE_NATURE);
//	mStateFilterFlag = contains( ENUM_TRACE_POINT::TRACE_STATE_NATURE);
//	mStatemachineFilterFlag = contains(ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE);
//
//	mTransitionFilterFlag = contains(ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE);
//	mRoutineFilterFlag    = contains(ENUM_TRACE_POINT::TRACE_ROUTINE_NATURE);
//
//
//	mComFilterFlag = mInputFilterFlag || mOutputFilterFlag || containsCom();
//
//	mIOTraceFilterFlag = mComFilterFlag || mNewfreshFilterFlag;
//
//	mRunnableFilterFlag = mMachineFilterFlag
//			|| mStateFilterFlag      || mStatemachineFilterFlag
//			|| mTransitionFilterFlag || mRoutineFilterFlag
//			|| contains(ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE);
//}


/**
 * Filter Point Flags
 */
bool TraceFilter::contains(ENUM_TRACE_POINT::TRACE_NATURE nature,
		AVM_OPCODE op, AvmCode * aCode) const
{
	AvmCode::const_iterator it = aCode->begin();
	AvmCode::const_iterator endIt = aCode->end();
	for( ; it != endIt ; ++it )
	{
		if( contains(nature, op, (*it)) )
		{
			return( true );
		}
	}

	return( false );
}

bool TraceFilter::contains(ENUM_TRACE_POINT::TRACE_NATURE nature,
		AVM_OPCODE op, const BF & arg) const
{
	if( arg.is< TracePoint >() )
	{
		return( ((nature == ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) ||
						(arg.to_ptr< TracePoint >()->nature == nature)) &&
				((op == AVM_OPCODE_NULL) ||
						(arg.to_ptr< TracePoint >()->op == op)) );
	}

	else if( arg.is< AvmCode >() )
	{
		return( contains(nature, op, arg.to_ptr< AvmCode >()) );
	}

	else if( arg.is< TraceSequence >() )
	{
		BFList::const_iterator it = arg.to_ptr< TraceSequence >()->points.begin();
		BFList::const_iterator endIt = arg.to_ptr< TraceSequence >()->points.end();
		for( ; it != endIt ; ++it )
		{
			if( contains(nature, op, (*it)) )
			{
				return( true );
			}
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if TRACE POINT pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(TracePoint * filterTP, TracePoint * aTP)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( aTP->isVirtual() )
	{
		return( true );
	}
	else if( (filterTP->nature != ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) )
	{
		if( (filterTP->nature != aTP->nature) )
		{
			if( aTP->nature == ENUM_TRACE_POINT::TRACE_MACHINE_NATURE )
			{
				if( filterTP->nature == ENUM_TRACE_POINT::TRACE_STATE_NATURE )
				{
					if( (aTP->object != NULL)
						&& (not aTP->object->to< InstanceOfMachine >()->
								getSpecifier().isFamilyComponentState()) )
					{
						return( false );
					}
				}
				else if( filterTP->nature ==
						ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE )
				{
					if( (aTP->object != NULL)
						&& (not aTP->object->to< InstanceOfMachine >()->
							getSpecifier().isComponentStatemachine()) )
//						&& (not aTP->object->to< InstanceOfMachine >()->
//							getSpecifier().isMocStateTransitionStructure()) )
					{
						return( false );
					}
				}
			}

			else if( (filterTP->nature != ENUM_TRACE_POINT::TRACE_COM_NATURE)
					|| (not ENUM_TRACE_POINT::is_com(aTP->nature)) )
			{
				return( false );
			}
		}
	}

	if( (filterTP->op != AVM_OPCODE_NULL) && (filterTP->op != aTP->op) )
	{
		switch( filterTP->op )
		{
			case AVM_OPCODE_INPUT:
			{
				switch( aTP->op )
				{
					case AVM_OPCODE_INPUT:
					case AVM_OPCODE_INPUT_BROADCAST:
					case AVM_OPCODE_INPUT_BUFFER:
					case AVM_OPCODE_INPUT_ENV:
					case AVM_OPCODE_INPUT_FLOW:
					case AVM_OPCODE_INPUT_FROM:
					case AVM_OPCODE_INPUT_MULTI_RDV:
					case AVM_OPCODE_INPUT_RDV:
					case AVM_OPCODE_INPUT_DELEGATE:
					case AVM_OPCODE_INPUT_VAR:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			case AVM_OPCODE_OUTPUT:
			{
				switch( aTP->op )
				{
					case AVM_OPCODE_OUTPUT:
					case AVM_OPCODE_OUTPUT_BROADCAST:
					case AVM_OPCODE_OUTPUT_BUFFER:
					case AVM_OPCODE_OUTPUT_ENV:
					case AVM_OPCODE_OUTPUT_FLOW:
					case AVM_OPCODE_OUTPUT_MULTI_RDV:
					case AVM_OPCODE_OUTPUT_RDV:
					case AVM_OPCODE_OUTPUT_TO:
					case AVM_OPCODE_OUTPUT_DELEGATE:
					case AVM_OPCODE_OUTPUT_VAR:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			case AVM_OPCODE_ENABLE_SET:
			{
				switch( aTP->op )
				{
					case AVM_OPCODE_RUN:
					case AVM_OPCODE_IRUN:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			default:
			{
				return( false );
			}
		}
	}

	if( (filterTP->machine != NULL) && (filterTP->machine != aTP->machine) )
	{
		if( aTP->config != NULL )
		{
			if( filterTP->machine->getSpecifier().isDesignModel() )
			{
				RuntimeID aRID = aTP->config->getRuntimeID();

				while( aRID.valid()
					&& (aRID.getModelInstance() != filterTP->machine) )
				{
					aRID = aRID.getPRID();
				}

				if( aRID.invalid() )
				{
					return( false );
				}
			}
			else
			{
				RuntimeID aRID = aTP->config->getRuntimeID();

				while( aRID.valid() &&
						(aRID.getInstance() != filterTP->machine) )
				{
					aRID = aRID.getPRID();
				}

				if( aRID.invalid() )
				{
					return( false );
				}
			}
		}
	}

	if( (filterTP->object != NULL) && (filterTP->object != aTP->object) )
	{
		return( false );
	}

	if( filterTP->value.valid() && filterTP->value.isEQ(aTP->value) )
	{
		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if VARIABLE pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const RuntimeID & aRID, InstanceOfData * aVariable)
{
	if( listOfVariableTracePoint.nonempty() )
	{
		ListOfTracePoint::const_iterator it = listOfVariableTracePoint.begin();
		ListOfTracePoint::const_iterator itEnd = listOfVariableTracePoint.end();

		for( ; it != itEnd ; ++it )
		{
			if( pass(*it, aRID, aVariable) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceFilter::pass(TracePoint * filterTP,
		const RuntimeID & aRID, InstanceOfData * aVariable)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		if( filterTP->nature == ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE )
		{
			if( filterTP->op == AVM_OPCODE_ASSIGN )
			{
				//!! IGNORED
			}


			if( (filterTP->machine == NULL)
				|| ( (filterTP->machine == aRID.getInstance())
					&& filterTP->machine->getSpecifier().hasDesignInstance() )
				|| ( (filterTP->machine->getExecutable() == aRID.getExecutable())
					&& filterTP->machine->getSpecifier().hasDesignModel() ) )
			{
				return( filterTP->any_object ||
						(filterTP->object == aVariable) );
			}
		}

		return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if Execution Trace
// a.k.a. ExecutionConfiguration pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(TracePoint * filterTP,
		ExecutionConfiguration * anExecConfTP)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( anExecConfTP->isAvmCode() )
	{
		return( pass(filterTP, anExecConfTP->getAvmCode()) );
	}
	else if( anExecConfTP->isTransition() )
	{
		return( pass(filterTP, anExecConfTP->getRuntimeID(),
				anExecConfTP->getTransition()) );
	}
	else if( anExecConfTP->isOperator() && (filterTP->op != AVM_OPCODE_NULL) )
	{
		AVM_OPCODE opcodeTP = anExecConfTP->getOperator()->getOptimizedOpCode();

		if( (filterTP->op != AVM_OPCODE_NULL) && (filterTP->op != opcodeTP ) )
		{
			switch( filterTP->op )
			{
				case AVM_OPCODE_ENABLE_SET:
				{
					switch( opcodeTP )
					{
						case AVM_OPCODE_RUN:
						case AVM_OPCODE_IRUN:
						{
							break;
						}
						default:
						{
							return( false );
						}
					}
					break;
				}
				default:
				{
					return( false );
				}
			}
		}

		if( (filterTP->machine == NULL)
			|| ( (filterTP->machine ==
					anExecConfTP->getRuntimeID().getInstance())
				&& filterTP->machine->getSpecifier().hasDesignInstance() )
			|| ( (filterTP->machine->getExecutable() ==
					anExecConfTP->getRuntimeID().getExecutable())
				&& filterTP->machine->getSpecifier().hasDesignModel() ) )
		{
			return( true );
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if a Compiled Element pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(TracePoint * filterTP,
		const RuntimeID & aRID, BaseCompiledForm * anElement)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( (filterTP->machine == NULL)
		|| ( (filterTP->machine == aRID.getInstance())
			&& filterTP->machine->getSpecifier().hasDesignInstance() )
		|| ( (filterTP->machine->getExecutable() == aRID.getExecutable())
			&& filterTP->machine->getSpecifier().hasDesignModel() ) )
	{
		return( filterTP->any_object ||
				(filterTP->object == anElement) );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if a Runtime Machine ID pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(TracePoint * filterTP, const RuntimeID & aRID)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	switch( filterTP->nature )
	{
		case ENUM_TRACE_POINT::TRACE_RUNNABLE_NATURE:
		case ENUM_TRACE_POINT::TRACE_MACHINE_NATURE:
		{
			break;
		}

		case ENUM_TRACE_POINT::TRACE_STATE_NATURE:
		{
			if( not aRID.getSpecifier().isFamilyComponentState() )
			{
				return( false );
			}
			break;
		}

		case ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE:
		{
			if( (not aRID.getSpecifier().isComponentStatemachine()) )
//				&& (not aRID.getSpecifier().isMocStateTransitionStructure()) )
			{
				return( false );
			}
			break;
		}

		default:
		{
			return( false );
		}
	}

	if( filterTP->machine == NULL )
	{
		return( filterTP->any_object
				|| (filterTP->object == aRID.getInstance()) );
	}
	else
	{
		return( ( (filterTP->machine == aRID.getInstance())
				&& filterTP->machine->getSpecifier().hasDesignInstance() )
			|| ( (filterTP->machine->getExecutable() == aRID.getExecutable())
				&& filterTP->machine->getSpecifier().hasDesignModel() ) );
	}

	return( false );
}

////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if AVM CODE pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(TracePoint * filterTP, AvmCode * aCodeTP)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP->toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	AVM_OPCODE opcodeTP = aCodeTP->getOptimizedOpCode();

	if( (filterTP->op != AVM_OPCODE_NULL) && (filterTP->op != opcodeTP ) )
	{
		switch( filterTP->op )
		{
			case AVM_OPCODE_INPUT:
			{
				switch( opcodeTP )
				{
					case AVM_OPCODE_INPUT:
					case AVM_OPCODE_INPUT_BROADCAST:
					case AVM_OPCODE_INPUT_BUFFER:
					case AVM_OPCODE_INPUT_ENV:
					case AVM_OPCODE_INPUT_FLOW:
					case AVM_OPCODE_INPUT_FROM:
					case AVM_OPCODE_INPUT_MULTI_RDV:
					case AVM_OPCODE_INPUT_RDV:
					case AVM_OPCODE_INPUT_DELEGATE:
					case AVM_OPCODE_INPUT_VAR:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			case AVM_OPCODE_OUTPUT:
			{
				switch( opcodeTP )
				{
					case AVM_OPCODE_OUTPUT:
					case AVM_OPCODE_OUTPUT_BROADCAST:
					case AVM_OPCODE_OUTPUT_BUFFER:
					case AVM_OPCODE_OUTPUT_ENV:
					case AVM_OPCODE_OUTPUT_FLOW:
					case AVM_OPCODE_OUTPUT_MULTI_RDV:
					case AVM_OPCODE_OUTPUT_RDV:
					case AVM_OPCODE_OUTPUT_TO:
					case AVM_OPCODE_OUTPUT_DELEGATE:
					case AVM_OPCODE_OUTPUT_VAR:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			case AVM_OPCODE_ENABLE_SET:
			{
				switch( opcodeTP )
				{
					case AVM_OPCODE_RUN:
					case AVM_OPCODE_IRUN:
					{
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			default:
			{
				return( false );
			}
		}
	}

	if( aCodeTP->empty() )
	{
		return( true );
	}

	if( (filterTP->machine != NULL)
		&& (aCodeTP->first() == filterTP->machine) )
	{
		return( true );
	}

	if( (filterTP->object != NULL)
		&& (aCodeTP->first() == filterTP->object) )
	{
		return( true );
	}

	if( filterTP->value.valid() && aCodeTP->populated() )
	{
		if( filterTP->value.is< ArrayBF >() )
		{
			const ArrayBF & arrayValue = filterTP->value.to_ref< ArrayBF >();
			avm_size_t arraySize = arrayValue.size();

			if( arraySize == aCodeTP->size() )
			{
				AvmCode::const_iterator itTP = aCodeTP->begin();

				for( avm_size_t offset = 0 ;
						(offset < arraySize) ; ++offset , ++itTP )
				{
					if( not (*itTP).isEQ( arrayValue[offset] ) )
					{
						return( false );
					}
				}

				return( true );
			}
			else
			{
				return( false );
			}
		}
		else
		{
			return( filterTP->value.isEQ( aCodeTP->second() ) );
		}
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void TraceFilter::toStream(OutStream & os) const
{
	os << TAB << "filter { "
			<< OperatorLib::to_string(mainTracePointFiter.getAvmOpCode())
			<< EOL_INCR_INDENT;

	AvmCode::const_iterator it = mainTracePointFiter.begin();
	AvmCode::const_iterator endIt = mainTracePointFiter.end();
	for( ; it != endIt ; ++it )
	{
		(*it).toStream(os);
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;

	os << TAB << "flag [ " << EOL_INCR_INDENT
		<< TAB << "Condition  : [ " << mConditionFlag
		<< " , decision:" << mDecisionFlag
		<< " ]"<< EOL

		<< TAB << "Trace_cond : [ path:" << mPathConditionFlag
		<< " , node:" << mNodeConditionFlag
		<< " ]"<< EOL

		<< TAB << "Timed_cond : [ path:" << mPathTimedConditionFlag
		<< " , node:" << mNodeTimedConditionFlag
		<< " ]"<< EOL

		<< TAB << "Leaf_cond  : [ path:" << mPathConditionLeafNodeFlag
		<< " , timed:" << mPathTimedConditionLeafNodeFlag
		<< " ]"<< EOL

		<< TAB << "Variable   : [ time:" << mTimeFilterFlag
		<< " , assign:" << mAssignFilterFlag
		<< " , newfresh:" << mNewfreshFilterFlag
		<< " ]"<< EOL

		<< TAB << "Input      : [ " << mInputFilterFlag
		<< " , env:" << mInputEnvFilterFlag
		<< " , rdv:" << mInputRdvFilterFlag << " ]"<< EOL

		<< TAB << "Output     : [ " << mOutputFilterFlag
		<< " , env:" << mOutputEnvFilterFlag
		<< " , rdv:" << mOutputRdvFilterFlag
		<< " ]"<< EOL

		<< TAB << "Machine    : [ " << mMachineFilterFlag
		<< " , state:" << mStateFilterFlag
		<< " , statemachine:" << mStatemachineFilterFlag
		<< " ]"<< EOL

		<< TAB << "Routine    : [ " << mRoutineFilterFlag
		<< " , transition:" << mTransitionFilterFlag
		<< " ]"<< EOL

		<< TAB << "Abstract   : [ com:" << mComFilterFlag
		<< " , io#trace:" << mIOTraceFilterFlag
		<< " , runnable:" << mRunnableFilterFlag
		<< " ]"<< EOL
		<< DECR_INDENT_TAB << "]" << EOL_FLUSH;
}




} /* namespace sep */
