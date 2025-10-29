/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BehavioralPart.h"

#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementFactory.h>

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Transition.h>

#include <fml/operator/OperatorManager.h>

#include <fml/template/TimedMachine.h>

#include <fml/type/TypeManager.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * TIME ROUTINE CONSTANT
 */
std::string BehavioralPart::ROUTINE_ID_TIME_GET ( "time#get"  );
std::string BehavioralPart::ROUTINE_ID_DELTA_GET( "delta#get" );

std::string BehavioralPart::ROUTINE_ID_TIME_RESET( "time#reset" );

std::string BehavioralPart::ROUTINE_ID_CLOCK_RESET ( "clock#reset"  );
std::string BehavioralPart::ROUTINE_ID_CLOCK_UPDATE( "clock#update" );

std::string BehavioralPart::VARIABLE_ID_CLOCK_INDEX( "_clock_index_" );

std::string BehavioralPart::ROUTINE_ID_VECTOR_CLOCK_RESET ( "clock#reset#vector"  );
std::string BehavioralPart::ROUTINE_ID_VECTOR_CLOCK_UPDATE( "clock#update#vector" );

std::string BehavioralPart::ROUTINE_ID_TIME_UPDATE( "time#update"  );


/**
 * GETTER - SETTER
 * onInitRoutine
 */
bool BehavioralPart::hasOnInitMachine() const
{
	if( hasOnInit() )
	{
		if( getOnInit()->isOpCode(AVM_OPCODE_INIT)
				&& getOnInit()->getOperands().singleton()
				&& getOnInit()->first().is< Machine >() )
		{
			return true;
		}
		else
		{
			return StatementFactory::hasActivityMachine(
					AVM_OPCODE_INIT, getOnInit() );
		}
	}


	return false;
}


/**
 * DISPATCH
 * mOwnedElements
 */
void BehavioralPart::dispatchOwnedElement(BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	ObjectElement & objElement = anElement.to< ObjectElement >();

	switch( anElement.classKind() )
	{
		// PROPERTY ELEMENT
		case FORM_XFSP_TRANSITION_KIND:
		{
			objElement.setRuntimeOffset( mOutgoingTransitions.size() );

			mOutgoingTransitions.append( anElement );

			break;
		}

		case FORM_XFSP_ROUTINE_KIND:
		{
			objElement.setRuntimeOffset( mRoutines.size() );

			mRoutines.append( anElement );
			break;
		}

		default:
		{ // TODO
			AVM_OS_FATAL_ERROR_EXIT
					<< "dispatchOwnedElement() unexpected object, typeinfo: "
					<< anElement.classKindInfo() << "\n\t<< "
					<< anElement.to< ObjectElement >().strHeader()
					<< " >> !!!"
					<< SEND_EXIT;
			break;
		}
	}
}


/**
 * GETTER - SETTER
 * mOwnedBehaviors
 */
void BehavioralPart::appendOwnedBehavior(Machine * aBehavior)
{
	mOwnedBehaviors.append( INCR_BF(aBehavior) );
}


/**
 * UTIL
 */
Routine & BehavioralPart::getActivity(AVM_OPCODE opcodeActivity)
{
	switch( opcodeActivity )
	{
		case AVM_OPCODE_INVOKE_NEW : return( onCreateRoutine  );

		case AVM_OPCODE_INIT   : return( onInitRoutine  );
		case AVM_OPCODE_FINAL  : return( onReturnRoutine );

		case AVM_OPCODE_RETURN : return( onReturnRoutine );

		case AVM_OPCODE_START  : return( onStartRoutine );
		case AVM_OPCODE_STOP   : return( onStopRoutine  );

		case AVM_OPCODE_IENABLE_INVOKE : return( onIEnableRoutine );
		case AVM_OPCODE_ENABLE_INVOKE  : return( onEnableRoutine  );

		case AVM_OPCODE_IDISABLE_INVOKE: return( onIDisableRoutine );
		case AVM_OPCODE_DISABLE_INVOKE : return( onDisableRoutine  );

		case AVM_OPCODE_IABORT_INVOKE  : return( onIAbortRoutine );
		case AVM_OPCODE_ABORT_INVOKE   : return( onAbortRoutine  );

		case AVM_OPCODE_IRUN: return( onIRunRoutine );
		case AVM_OPCODE_RUN : return( onRunRoutine  );
		case AVM_OPCODE_RTC : return( onRtcRoutine  );

		case AVM_OPCODE_SCHEDULE_INVOKE: return( onScheduleRoutine );

		case AVM_OPCODE_SYNCHRONIZE    : return( onSynchronizeRoutine );

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BehavioralPart::getActivity:> Unknown Activity !!!"
					<< SEND_EXIT;

			return( onRunRoutine );
		}
	}
}

const Routine & BehavioralPart::getActivity(AVM_OPCODE opcodeActivity) const
{
	switch( opcodeActivity )
	{
		case AVM_OPCODE_INVOKE_NEW    : return( onCreateRoutine  );

		case AVM_OPCODE_INIT   : return( onInitRoutine  );
		case AVM_OPCODE_FINAL  : return( onReturnRoutine );

		case AVM_OPCODE_RETURN : return( onReturnRoutine );

		case AVM_OPCODE_START  : return( onStartRoutine );
		case AVM_OPCODE_STOP   : return( onStopRoutine  );

		case AVM_OPCODE_IENABLE_INVOKE : return( onIEnableRoutine );
		case AVM_OPCODE_ENABLE_INVOKE  : return( onEnableRoutine  );

		case AVM_OPCODE_IDISABLE_INVOKE: return( onIDisableRoutine );
		case AVM_OPCODE_DISABLE_INVOKE : return( onDisableRoutine  );

		case AVM_OPCODE_IABORT_INVOKE  : return( onIAbortRoutine );
		case AVM_OPCODE_ABORT_INVOKE   : return( onAbortRoutine  );

		case AVM_OPCODE_IRUN: return( onIRunRoutine );
		case AVM_OPCODE_RUN : return( onRunRoutine  );
		case AVM_OPCODE_RTC : return( onRtcRoutine  );

		case AVM_OPCODE_SCHEDULE_INVOKE: return( onScheduleRoutine );

		case AVM_OPCODE_SYNCHRONIZE    : return( onSynchronizeRoutine );

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BehavioralPart::getActivity:> Unknown Activity !!!"
					<< SEND_EXIT;

			return( onRunRoutine );
		}
	}
}


/**
 * ADD
 * [ delta ] time property
 */
void BehavioralPart::addTimeSupport(PropertyPart & aPropertyPart)
{
	const BF & timeVar = aPropertyPart.exprTimeVariable();

	const BF & deltaVar = aPropertyPart.exprDeltaTimeVariable();

	// time & delta getters ;
	// clock << reset & update >> routine macro
	// time getter routine macro
	Routine * timeGetter = Routine::newDefine(*this, ROUTINE_ID_TIME_GET);
	timeGetter->getwModifier().setNatureMacro(true);
	saveRoutine( timeGetter );

	Modifier mdfrReturn(
			Modifier::VISIBILITY_PRIVATE_KIND,
			Modifier::DIRECTION_RETURN_KIND,
			Modifier::NATURE_PARAMETER_KIND,
			Modifier::FEATURE_TRANSIENT_KIND );

	Variable * paramVariable = new Variable(timeGetter,
			mdfrReturn, aPropertyPart.getTimeType(), "_time_");
	timeGetter->getPropertyPart().saveOwnedVariableReturn(paramVariable);
	timeGetter->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_RETURN, timeVar ) );

	// time getter routine macro
	Routine * deltaGetter = Routine::newDefine(*this, ROUTINE_ID_DELTA_GET);
	deltaGetter->getwModifier().setNatureMacro(true);
	saveRoutine( deltaGetter );

	paramVariable = new Variable(deltaGetter, mdfrReturn,
			aPropertyPart.getDeltaTimeType(), "_delta_");
	deltaGetter->getPropertyPart().saveOwnedVariableReturn(paramVariable);
	deltaGetter->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_RETURN, deltaVar ) );


	// global time << reset >> routine macro
	Routine * timeReset = Routine::newDefine(*this, ROUTINE_ID_TIME_RESET);
	timeReset->getwModifier().setNatureMacro(true);
	saveRoutine( timeReset );

	timeReset->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, timeVar,
			ExpressionConstant::INTEGER_ZERO ) );


//	TypeSpecifier clockType( TypeManager::newClockTime(
//			TYPE_CLOCK_SPECIFIER, TypeManager::UINTEGER) );
	TypeSpecifier clockType( TypeManager::newClockTime(TYPE_CLOCK_SPECIFIER,
			TimedMachine::timeTypeSpecifier(
					aPropertyPart.getContainerMachine()->getSpecifier())) );

	// clock << reset >> routine macro
	Routine * clockReset = Routine::newDefine(*this, ROUTINE_ID_CLOCK_RESET);
	clockReset->getwModifier().setNatureMacro(true);
	saveRoutine( clockReset );

	Modifier mdfrParam(
			Modifier::VISIBILITY_PRIVATE_KIND,
			Modifier::DIRECTION_INOUT_KIND,
			Modifier::NATURE_PARAMETER_KIND);

	paramVariable = new Variable(clockReset, mdfrParam, clockType, "_clock_");
	clockReset->getPropertyPart().saveOwnedVariableParameter( paramVariable );
	clockReset->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, INCR_BF(paramVariable),
			ExpressionConstant::INTEGER_ZERO ) );


	// clock << update >> routine macro
	Routine * clockUpdate = Routine::newDefine(*this, ROUTINE_ID_CLOCK_UPDATE);
	clockUpdate->getwModifier().setNatureMacro(true);
	saveRoutine( clockUpdate );

	paramVariable = new Variable(clockUpdate, mdfrParam, clockType, "_clock_");
	clockUpdate->getPropertyPart().saveOwnedVariableParameter( paramVariable );
	clockUpdate->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, INCR_BF(paramVariable),
			ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_PLUS,
					INCR_BF(paramVariable), deltaVar) ) );


	// index for vector of clock
	Modifier mdfrTimed;

	Variable * aClockIndex = new Variable(aPropertyPart.getContainer(),
			mdfrTimed, TypeManager::UINT, VARIABLE_ID_CLOCK_INDEX,
			ExpressionConstant::INTEGER_ZERO);

	const BF & bfClockIndex = aPropertyPart.saveOwnedVariable( aClockIndex );


	// vector of clock << reset >> routine macro
	clockReset = Routine::newDefine(*this, ROUTINE_ID_VECTOR_CLOCK_RESET);
	clockReset->getwModifier().setNatureMacro(true);
	saveRoutine( clockReset );

	TypeSpecifier clockVectorType(
			TypeManager::newCollection(DataType::nullref(),
					TYPE_VECTOR_SPECIFIER, clockType, AVM_NUMERIC_MAX_SIZE_T) );

	paramVariable = new Variable(
			clockReset, mdfrParam, clockVectorType, "_clock_vector_");
	clockReset->getPropertyPart().saveOwnedVariableParameter( paramVariable );

	UniFormIdentifier * ufi;
	BF clockAtIndex( ufi = new UniFormIdentifier(false) );
	ufi->appendFieldVariable( INCR_BF(paramVariable) );
	ufi->appendIndex( bfClockIndex );

	clockReset->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_FOR,
			// Initialisation
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN,
					bfClockIndex, ExpressionConstant::INTEGER_ZERO ),
			// Condition
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_LT,
					bfClockIndex,
					ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_SIZE,
							INCR_BF(paramVariable) ) ),
			// Incrementation
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN,
					bfClockIndex,
					ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_PLUS,
							bfClockIndex, ExpressionConstant::INTEGER_ONE) ),
			// Instruction
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN, clockAtIndex,
					ExpressionConstant::INTEGER_ZERO) ) );


	// vector of clock << update >> routine macro
	clockUpdate = Routine::newDefine(*this, ROUTINE_ID_VECTOR_CLOCK_UPDATE);
	clockUpdate->getwModifier().setNatureMacro(true);
	saveRoutine( clockUpdate );

	paramVariable = new Variable(
			clockUpdate, mdfrParam, clockVectorType, "_clock_vector_");
	clockUpdate->getPropertyPart().saveOwnedVariableParameter( paramVariable );

	clockAtIndex = ufi = new UniFormIdentifier(false);
	ufi->appendFieldVariable( INCR_BF(paramVariable) );
	ufi->appendIndex( bfClockIndex );

	clockUpdate->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_FOR,
			// Initialisation
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN,
					bfClockIndex, ExpressionConstant::INTEGER_ZERO ),
			// Condition
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_LT,
					bfClockIndex,
					ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_SIZE,
							INCR_BF(paramVariable) ) ),
			// Incrementation
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN,
					bfClockIndex,
					ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_PLUS,
							bfClockIndex, ExpressionConstant::INTEGER_ONE) ),
			// Instruction
			StatementConstructor::newCode(
					OperatorManager::OPERATOR_ASSIGN,
					clockAtIndex,
					ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_PLUS,
							clockAtIndex, deltaVar) ) ) );
}


/**
 * Serialization
 */
void BehavioralPart::toStreamRoutine(OutStream & out) const
{
	out << TAB << "@routine:" << EOL_INCR_INDENT;

	routine_iterator it = mRoutines.begin();
	routine_iterator endIt = mRoutines.end();
	for( ; it != endIt ; ++it )
	{
		(it)->toStream(out);
	}

	out << DECR_INDENT;
}

void BehavioralPart::toStreamAnonymousInnerRoutine(OutStream & out) const
{
	out << TAB << "/*routine< anonymous#inner >: [" << EOL;

	routine_iterator it = mAnonymousInnerRoutines.begin();
	routine_iterator endIt = mAnonymousInnerRoutines.end();
	for( ; it != endIt ; ++it )
	{
		out << TAB2 << (it)->getFullyQualifiedNameID() << ";" << EOL;
//		out << TAB2 << str_header( *it ) << ";" << EOL;
	}
	out << TAB << "] // end routine" << "*/" << EOL_FLUSH;
}


void BehavioralPart::toStreamMoe(OutStream & out) const
{
	/**
	 * mOwned Behaviors
	 */
	if( hasOwnedBehavior() )
	{
		out << TAB << "@behavior:" << EOL;
		for( const auto & itBehavior : getOwnedBehaviors() )
		{
			out << TAB2 << str_header( itBehavior ) << ";" << EOL;
		}
		out << EOL_FLUSH;
	}

	/**
	 * Transitions Part
	 */
	if( hasOutgoingTransition() )
	{
		if( not getContainerMachine()->getSpecifier().isStateBasic() )
		{
			out << TAB << "@transition" /*<< "< outgoing >"*/ << ":" << EOL;
		}

		out << INCR_INDENT;
		for( const auto & itTransition : getOutgoingTransitions() )
		{
			itTransition.toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasIncomingTransition() )
	{
		out << TAB << "/*transition< incoming >: [" << EOL_INCR_INDENT;
		for( const auto & itTransition : getIncomingTransitions() )
		{
			out << TAB2 << str_header( itTransition ) << ";" << EOL;
		}
		out << DECR_INDENT_TAB << "] // end transition" << "*/" << EOL_FLUSH;
	}


	if( getContainer()->isnot< Machine >() ||
		(not getContainerMachine()->getSpecifier().isStateBasic()) )
	{
		out << TAB << "@" << getNameID() << ":" << EOL;
	}

	/**
	 * Routines Part
	 */
	out << INCR_INDENT;

	if( hasOnCreate() )
	{
		getOnCreateRoutine().toStream(out);
	}

	if( hasOnInit() )
	{
		getOnInitRoutine().toStream(out);
	}

	if( hasOnFinal() )
	{
		getOnFinalRoutine().toStream(out);
	}

	if( hasOnReturn() )
	{
		getOnReturnRoutine().toStream(out);
	}


	if( hasOnStart() )
	{
		getOnStartRoutine().toStream(out);
	}

	if( hasOnStop() )
	{
		getOnStopRoutine().toStream(out);
	}


	if( hasOnIEnable() )
	{
		getOnIEnableRoutine().toStream(out);
	}

	if( hasOnEnable() )
	{
		getOnEnableRoutine().toStream(out);
	}


	if( hasOnIDisable() )
	{
		getOnIDisableRoutine().toStream(out);
	}

	if( hasOnDisable() )
	{
		getOnDisableRoutine().toStream(out);
	}


	if( hasOnIAbort() )
	{
		getOnIAbortRoutine().toStream(out);
	}

	if( hasOnAbort() )
	{
		getOnAbortRoutine().toStream(out);
	}


	if( hasOnIRun() )
	{
		getOnIRunRoutine().toStream(out);
	}

	if( hasOnRun() )
	{
		getOnRunRoutine().toStream(out);
	}


	if( hasOnRtc() )
	{
		getOnRtcRoutine().toStream(out);
	}


	if( hasOnConcurrency() )
	{
		getOnConcurrencyRoutine().toStream(out);
	}

	if( hasOnSchedule() )
	{
		getOnScheduleRoutine().toStream(out);
	}

	if( hasOnSynchronize() )
	{
		getOnSynchronizeRoutine().toStream(out);
	}

	out << DECR_INDENT;
}



}
