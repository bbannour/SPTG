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
#include <fml/runtime/ExecutionInformation.h>

#include <fml/trace/TraceFactory.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
TraceFilter::TraceFilter(const std::string & aNameID)
: mNameID( aNameID ),
mainTracePointFiter( OperatorManager::OPERATOR_OR ),

listOfBufferTracePoint( ),
listOfVariableTracePoint( ),

////////////////////////////////////////////////////////////////////////////
// Computing Variables
objectDeltaTime( nullptr ),

mStepHeaderSeparatorFlag( false ),
mStepBeginSeparatorFlag( false ),
mStepEndSeparatorFlag( false ),

mConditionFlag( false ),
mDecisionFlag( false ),

mPathConditionFlag( false ),
mPathTimedConditionFlag( false ),

mPathConditionLeafNodeFlag( false ),
mPathTimedConditionLeafNodeFlag( false ),

mNodeConditionFlag( false ),
mNodeTimedConditionFlag( false ),

mNodeConditionLeafNodeFlag( false ),
mNodeTimedConditionLeafNodeFlag( false ),

mTimeFilterFlag( false ),
mAssignFilterFlag( false ),
mNewfreshFilterFlag( false ),

mInputEnvFilterFlag( false ),
mInputRdvFilterFlag( false ),

mInputExternalFilterFlag( false ),
mInputInternalFilterFlag( false ),
mInputFilterFlag( false ),

mOutputEnvFilterFlag( false ),
mOutputRdvFilterFlag( false ),

mOutputExternalFilterFlag( false ),
mOutputInternalFilterFlag( false ),
mOutputFilterFlag( false ),

mMachineFilterFlag( false ),
mStateFilterFlag( false ),
mStatemachineFilterFlag( false ),
mTransitionFilterFlag( false ),
mRoutineFilterFlag( false ),

mComExternalFilterFlag( false ),
mComInternalFilterFlag( false ),
mComFilterFlag( false ),

mComBufferFilterFlag( false ),

mMetaInformalFilterFlag( false ),
mMetaTraceFilterFlag( false ),
mMetaDebugFilterFlag( false ),

mIOTraceFilterFlag( false ),
mRunnableFilterFlag( false ),

mExecutionInformationFilterFlag( false )
{
	//!! NOTHING
}



/**
 * [RE]SET TracePoint ID
 */
void TraceFilter::resetTracePointID()
{
	for( auto & itPoint : mainTracePointFiter.getOperands() )
	{
		resetTracePointID( itPoint );
	}

	for( auto & itPoint : listOfVariableTracePoint )
	{
		itPoint->to< TracePoint >().tpid = 0;
	}
	for( auto & itPoint : listOfBufferTracePoint )
	{
		itPoint->to< TracePoint >().tpid = 0;
	}
}

void TraceFilter::resetTracePointID(BF & point)
{
	if( point.is< TracePoint >() )
	{
		point.to< TracePoint >().tpid = 0;
	}
	else if( point.is< AvmCode >() )
	{
		for( auto & itPoint :point.to< AvmCode >().getOperands() )
		{
			resetTracePointID( itPoint );
		}
	}
}

void TraceFilter::setTracePointID(std::size_t intialTPID)
{
	for( auto & itPoint : mainTracePointFiter.getOperands() )
	{
		setTracePointID( itPoint , intialTPID );
	}

	for( auto & itPoint : listOfVariableTracePoint )
	{
		itPoint->to< TracePoint >().tpid = intialTPID++;
	}
	for( auto & itPoint : listOfBufferTracePoint )
	{
		itPoint->to< TracePoint >().tpid = intialTPID++;
	}
}

void TraceFilter::setTracePointID(BF & point, std::size_t & intialTPID)
{
	if( point.is< TracePoint >() )
	{
		point.to< TracePoint >().tpid = intialTPID++;
	}
	else if( point.is< AvmCode >() )
	{
		for( auto & itPoint :point.to< AvmCode >().getOperands() )
		{
			setTracePointID( itPoint , intialTPID );
		}
	}
}



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

#define LEAF_PATH_REGEX_PATTERN     "(leaf|end|last|tail)"

#define LEAF_NODE_REGEX_PATTERN     "\\S?(leaf|end|last|tail)\\S?"

#define LEAF_NODE_DEFAULT_PATTERN   ":leaf:"


bool TraceFilter::configure(EvaluationEnvironment & ENV,
		const WObject * wfParameterObject, const WObject * wfTraceObject)
{
	if( TimedMachine::SYSTEM_VAR_DELTA_TIME != nullptr )
	{
		ExecutableQuery XQuery( ENV.getConfiguration() );

		objectDeltaTime = XQuery.getVariableByAstElement(
			(* TimedMachine::SYSTEM_VAR_DELTA_TIME)).to_ptr< InstanceOfData >();
	}

	// default main combinator
	mainTracePointFiter.setOperator( OperatorManager::OPERATOR_OR );

	// Configuration of TRACE
	TraceFactory traceFactory(ENV.getConfiguration(),
			ENV, wfParameterObject, ExecutableForm::nullref(), objectDeltaTime);
	if( not traceFactory.configure(
			wfTraceObject, mainTracePointFiter.getOperands()) )
	{
//		return( false );
	}

	listOfBufferTracePoint.append( traceFactory.getBufferTracePoints() );

	listOfVariableTracePoint.append( traceFactory.getVariableTracePoints() );


	// Initialize Filter Point Flags
	mStepHeaderSeparatorFlag = Query::hasRegexWProperty(
			wfTraceObject, CONS_WID2("step", "header"));

	mStepBeginSeparatorFlag = Query::hasRegexWProperty(
			wfTraceObject, CONS_WID2("step", "begin"));

	mStepEndSeparatorFlag = Query::hasRegexWProperty(
			wfTraceObject, CONS_WID2("step", "end"));


	mExecutionInformationFilterFlag = Query::hasRegexWProperty(wfTraceObject,
			ENUM_TRACE_POINT::ATTRIBUTE_EXECUTION_INFORMATION_ID);


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
					CONS_WID3("path", "condition", LEAF_PATH_REGEX_PATTERN))
				|| REGEX_MATCH(Query::getRegexWPropertyString(
							wfTraceObject, CONS_WID2("path", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );


		mNodeConditionFlag = not REGEX_MATCH(
				Query::getRegexWPropertyString(wfTraceObject,
					CONS_WID2("node", "condition"), LEAF_NODE_DEFAULT_PATTERN),
				LEAF_NODE_REGEX_PATTERN );

		mNodeConditionLeafNodeFlag = mNodeConditionFlag
				|| Query::hasRegexWProperty(wfTraceObject,
					CONS_WID3("node", "condition", LEAF_PATH_REGEX_PATTERN))
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
						"path", "timed", "condition", LEAF_PATH_REGEX_PATTERN) )
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
						"node", "timed", "condition", LEAF_PATH_REGEX_PATTERN) )
				|| REGEX_MATCH(Query::getRegexWPropertyString(wfTraceObject,
						CONS_WID3("node", "timed", "condition"), ""),
					LEAF_NODE_REGEX_PATTERN );
	}

	mTimeFilterFlag = Query::hasRegexWProperty(wfTraceObject, "\\S?time");

	mAssignFilterFlag = listOfVariableTracePoint.nonempty()
			|| Query::hasRegexWPropertyString(wfTraceObject, "var(iable)?")
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

	mComBufferFilterFlag = listOfBufferTracePoint.nonempty()
			|| Query::hasWPropertyString(wfTraceObject, "buffer");


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


	mMetaTraceFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "trace");

	mMetaDebugFilterFlag =
			Query::hasWPropertyString(wfTraceObject, "debug");


	resetIOTracePoint();

	resetRunnablePoint();


	// Update Filter Point Flags
	//updateFilterFlags();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , TRACE )
	AVM_OS_LOG << "TraceFilter:> "; toStream(AVM_OS_LOG);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , CONFIGURING , TRACE )

	return( true );
}


bool TraceFilter::configure(EvaluationEnvironment & ENV,
		const WObject * wfParameterObject,
		const std::string & aWSequenceNameID,
		const std::string & aWSequenceElseNameID)
{
	const WObject * theTRACE = Query::getWSequenceOrElse(
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
//	mComFilterFlag = mInputFilterFlag || mOutputFilterFlag || containsCom();
//
//  mComBufferFilterFlag = listOfBufferTracePoint.nonempty()
//			|| contains(ENUM_TRACE_POINT::TRACE_BUFFER_NATURE);
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
		AVM_OPCODE op, const AvmCode & aCode) const
{
	for( const auto & itOperand : aCode.getOperands() )
	{
		if( contains(nature, op, itOperand) )
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
						(arg.to< TracePoint >().nature == nature)) &&
				((op == AVM_OPCODE_NULL) ||
						(arg.to< TracePoint >().op == op)) );
	}

	else if( arg.is< AvmCode >() )
	{
		return( contains(nature, op, arg.to< AvmCode >()) );
	}

	else if( arg.is< TraceSequence >() )
	{
		for( const auto & itPoint : arg.to< TraceSequence >().points )
		{
			if( contains(nature, op, itPoint) )
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

bool TraceFilter::pass(const TracePoint & filterTP, const TracePoint & aTP) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( aTP.isVirtual() )
	{
		return( true );
	}
	else if( (filterTP.nature != ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE) )
	{
		if( (filterTP.nature != aTP.nature) )
		{
			if( aTP.nature == ENUM_TRACE_POINT::TRACE_MACHINE_NATURE )
			{
				if( filterTP.nature == ENUM_TRACE_POINT::TRACE_STATE_NATURE )
				{
					if( (aTP.object != nullptr)
						&& (not aTP.object->to_ptr< InstanceOfMachine >()->
								getSpecifier().isFamilyComponentState()) )
					{
						return( false );
					}
				}
				else if( filterTP.nature ==
						ENUM_TRACE_POINT::TRACE_STATEMACHINE_NATURE )
				{
					if( (aTP.object != nullptr)
						&& (not aTP.object->to_ptr< InstanceOfMachine >()->
							getSpecifier().isComponentStatemachine()) )
//						&& (not aTP.object->to_ptr< InstanceOfMachine >()->
//							getSpecifier().isMocStateTransitionStructure()) )
					{
						return( false );
					}
				}
			}

			else if( (filterTP.nature != ENUM_TRACE_POINT::TRACE_COM_NATURE)
					|| (not ENUM_TRACE_POINT::is_com(aTP.nature)) )
			{
				return( false );
			}
		}
	}

	if( (filterTP.op != AVM_OPCODE_NULL) && (filterTP.op != aTP.op) )
	{
		switch( filterTP.op )
		{
			case AVM_OPCODE_INPUT:
			{
				switch( aTP.op )
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
				switch( aTP.op )
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

			case AVM_OPCODE_ENABLE_INVOKE:
			case AVM_OPCODE_ENABLE_SET:
			{
				switch( aTP.op )
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

	if( (filterTP.machine != nullptr) && (filterTP.machine != aTP.machine) )
	{
		if( aTP.config.isnotNullref() )
		{
			if( filterTP.machine->getSpecifier().isDesignModel() )
			{
				RuntimeID aRID = aTP.config.getRuntimeID();

				while( aRID.valid()
					&& (aRID.getModelInstance() != filterTP.machine) )
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
				RuntimeID aRID = aTP.config.getRuntimeID();

				while( aRID.valid() &&
						(aRID.getInstance() != filterTP.machine) )
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

	if( (filterTP.object != nullptr) && (filterTP.object != aTP.object) )
	{
		return( false );
	}

	if( filterTP.value.valid() && filterTP.value.isEQ(aTP.value) )
	{
		return( false );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if TRANSITION pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP,
		const AvmTransition & aTransition) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB << "Transition :"
			<< (filterTP.object == (& aTransition))  << "  ";
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	return( (filterTP.nature == ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE)
			&& (filterTP.op == AVM_OPCODE_INVOKE_TRANSITION)
			&& (filterTP.any_object
//				|| (filterTP.object == nullptr)
				|| (filterTP.object == (& aTransition))) );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if BUFFER pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const RuntimeID & aRID,
		const InstanceOfBuffer & aBuffer) const
{
	if( listOfBufferTracePoint.nonempty() )
	{
		for( const auto & itTracePoint : listOfBufferTracePoint )
		{
			if( pass(*itTracePoint, aRID, aBuffer) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceFilter::pass(const TracePoint & filterTP,
		const RuntimeID & aRID, const InstanceOfBuffer & aBuffer) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		if( filterTP.nature == ENUM_TRACE_POINT::TRACE_BUFFER_NATURE )
		{
			if( filterTP.op == AVM_OPCODE_ASSIGN )
			{
				//!! IGNORED
			}

			if( filterTP.any_object
//				|| (filterTP.object == nullptr)
				|| (filterTP.object == (& aBuffer)) )
			{
				if( filterTP.RID.valid() )
				{
					return( aRID.hasAsAncestor(filterTP.RID) );
				}
				else
				{
					return( (filterTP.machine == nullptr)
						|| filterTP.machine->getSpecifier().isDesignModel()
						|| aRID.hasAsAncestor(* filterTP.machine) );
				}
			}
		}

		return( false );
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if VARIABLE pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const RuntimeID & aRID,
		const InstanceOfData & aVariable) const
{
	if( listOfVariableTracePoint.nonempty() )
	{
		for( const auto & itTracePoint : listOfVariableTracePoint )
		{
			if( pass(*itTracePoint, aRID, aVariable) )
			{
				return( true );
			}
		}
	}

	return( false );
}


bool TraceFilter::pass(const TracePoint & filterTP,
		const RuntimeID & aRID, const InstanceOfData & aVariable) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

		if( filterTP.nature == ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE )
		{
			if( filterTP.op == AVM_OPCODE_ASSIGN )
			{
				//!! IGNORED
			}

			if( filterTP.any_object
//				|| (filterTP.object == nullptr)
				|| (filterTP.object == (& aVariable)) )
			{
				if( filterTP.RID.valid() )
				{
					return( aRID.hasAsAncestor(filterTP.RID) );
				}
				else
				{
					return( (filterTP.machine == nullptr)
						|| filterTP.machine->getSpecifier().isDesignModel()
						|| aRID.hasAsAncestor(* filterTP.machine) );
				}
			}
		}

		return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if Execution Trace
// a.k.a. ExecutionConfiguration pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP,
		const ExecutionConfiguration & anExecConfTP) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( anExecConfTP.isAvmCode() )
	{
		return( pass(filterTP, anExecConfTP.toAvmCode()) );
	}
	else if( anExecConfTP.isTransition() )
	{
		return( pass(filterTP, anExecConfTP.getRuntimeID(),
				anExecConfTP.toTransition()) );
	}
	else if( anExecConfTP.isOperator() && (filterTP.op != AVM_OPCODE_NULL) )
	{
		AVM_OPCODE opcodeTP = anExecConfTP.getOperator().getOptimizedOpCode();

		if( (filterTP.op != AVM_OPCODE_NULL) && (filterTP.op != opcodeTP ) )
		{
			switch( filterTP.op )
			{
				case AVM_OPCODE_ENABLE_INVOKE:
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

		if( filterTP.RID.valid() )
		{
			return( anExecConfTP.getRuntimeID().hasAsAncestor(filterTP.RID) );
		}
		else
		{
			return( (filterTP.machine == nullptr)
				|| filterTP.machine->getSpecifier().isDesignModel()
				|| anExecConfTP.getRuntimeID().hasAsAncestor(* filterTP.machine) );
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if a Compiled Element pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(
		const TracePoint & filterTP, const ObjectElement & anElement) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	return( filterTP.any_object
//			|| (filterTP.object == nullptr)
			|| (filterTP.object == (& anElement)) );
}

bool TraceFilter::pass(const TracePoint & filterTP,
		const RuntimeID & aRID, const ObjectElement & anElement) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( filterTP.any_object
//		|| (filterTP.object == nullptr)
		|| (filterTP.object == (& anElement)) )
	{
		if( filterTP.RID.valid() )
		{
			return( aRID.hasAsAncestor(filterTP.RID) );
		}
		else
		{
			return( (filterTP.machine == nullptr)
				|| filterTP.machine->getSpecifier().isDesignModel()
				|| aRID.hasAsAncestor(* filterTP.machine) );
		}
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if an AST Element pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP, const Port & aPort) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	if( filterTP.any_object || (filterTP.object == (& aPort)) )
		//|| (filterTP.object == nullptr) )
	{
		return true;
	}
	else if( filterTP.object->is< InstanceOfPort >() )
	{
		return( filterTP.object->to< InstanceOfPort >().isAstElement(aPort) );
	}

	return false;
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if a Runtime Machine ID pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP, const RuntimeID & aRID) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	switch( filterTP.nature )
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

	if( filterTP.RID.valid() )
	{
		return( aRID.hasAsAncestor(filterTP.RID) );
	}
	else if( filterTP.machine == nullptr )
	{
		return( filterTP.any_object
//				|| (filterTP.object == nullptr)
				|| (filterTP.object == aRID.getInstance()) );
	}
	else
	{
		return( ( (filterTP.machine == aRID.getInstance())
				&& filterTP.machine->getSpecifier().hasDesignInstance() )
			|| ( (filterTP.machine->getExecutable() == aRID.getExecutable())
				&& filterTP.machine->getSpecifier().hasDesignModel() ) );
	}

	return( false );
}

////////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if AVM CODE pass
////////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP, const AvmCode & aCodeTP) const
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )
	AVM_OS_TRACE << TAB;
	filterTP.toStream(AVM_OS_TRACE << AVM_TAB_INDENT);
	AVM_OS_TRACE << END_INDENT;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRACE )

	AVM_OPCODE opcodeTP = aCodeTP.getOptimizedOpCode();

//	ENUM_TRACE_POINT::TRACE_NATURE nature =
//			ENUM_TRACE_POINT::TRACE_UNDEFINED_NATURE;

	if( (filterTP.op != AVM_OPCODE_NULL) && (filterTP.op != opcodeTP ) )
	{
		switch( filterTP.op )
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
//						nature = ENUM_TRACE_POINT::TRACE_COM_NATURE;
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
//						nature = ENUM_TRACE_POINT::TRACE_COM_NATURE;
						break;
					}

					default:
					{
						return( false );
					}
				}
				break;
			}

			case AVM_OPCODE_ENABLE_INVOKE:
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

	if( aCodeTP.noOperand() )
	{
		return( true );
	}

	if( (filterTP.machine != nullptr)
		&& (aCodeTP.first() == filterTP.machine) )
	{
		return( true );
	}

	if( (filterTP.object != nullptr)
		&& (aCodeTP.first() == filterTP.object) )
	{
		return( true );
	}

	if( filterTP.value.valid() && aCodeTP.hasManyOperands() )
	{
		if( filterTP.value.is< ArrayBF >() )
		{
			const ArrayBF & arrayValue = filterTP.value.to< ArrayBF >();
			std::size_t arraySize = arrayValue.size();

			if( arraySize == aCodeTP.size() )
			{
				AvmCode::const_iterator itOperandTP = aCodeTP.begin();

				for( std::size_t offset = 0 ;
						(offset < arraySize) ; ++offset , ++itOperandTP )
				{
					if( not (*itOperandTP).isEQ( arrayValue[offset] ) )
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
			return( filterTP.value.isEQ( aCodeTP.second() ) );
		}
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API : check if Execution Information pass
////////////////////////////////////////////////////////////////////////////

bool TraceFilter::pass(const TracePoint & filterTP,
		const ExecutionInformation & anExecInfoTP) const
{
	return true;
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void TraceFilter::toStream(OutStream & os) const
{
	os << TAB << "filter " << mNameID << " { "
			<< OperatorLib::to_string(mainTracePointFiter.getAvmOpCode())
			<< EOL_INCR_INDENT;

	for( const auto & itOperand : mainTracePointFiter.getOperands() )
	{
		itOperand.toStream(os);
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
		<< " , assign:"   << mAssignFilterFlag
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
		<< " , state:"        << mStateFilterFlag
		<< " , statemachine:" << mStatemachineFilterFlag
		<< " ]"<< EOL

		<< TAB << "Routine    : [ " << mRoutineFilterFlag
		<< " , transition:" << mTransitionFilterFlag
		<< " ]"<< EOL

		<< TAB << "Abstract   : [ com:" << mComFilterFlag
		<< " , io#trace:"  << mIOTraceFilterFlag
		<< " , runnable:"  << mRunnableFilterFlag
		<< " , exec#info:" << mExecutionInformationFilterFlag
		<< " ]"<< EOL

		<< TAB << "Meta:Stmnt : [ " << " @trace:" << mMetaTraceFilterFlag
		<< " , @debug:"    << mMetaDebugFilterFlag
		<< " ]"<< EOL

		<< TAB << "Meta:Step  : [ header:" << mStepHeaderSeparatorFlag
		<< " , begin:" << mStepBeginSeparatorFlag
		<< " , end:"   << mStepEndSeparatorFlag
		<< " ]"<< EOL
		<< DECR_INDENT_TAB << "]" << EOL_FLUSH;
}




} /* namespace sep */
