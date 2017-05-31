/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TimedMachine.h"

#include <parser/model/ParserUtil.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/operator/OperatorManager.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/type/TypeManager.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Routine.h>
#include <fml/infrastructure/Variable.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

std::string TimedMachine::VAR_ID_GLOBAL_TIME( "$time"  );
std::string TimedMachine::VAR_ID_DELTA_TIME ( "$delta" ); //"$time#delta"

std::string TimedMachine::ROUTINE_ID_TIME_GET ( "time#get"  );
std::string TimedMachine::ROUTINE_ID_DELTA_GET( "delta#get" );

std::string TimedMachine::ROUTINE_ID_TIME_RESET ( "time#reset"  );

std::string TimedMachine::ROUTINE_ID_CLOCK_RESET ( "clock#reset"  );
std::string TimedMachine::ROUTINE_ID_CLOCK_UPDATE( "clock#update" );

Variable * TimedMachine::SYSTEM_VAR_GLOBAL_TIME = NULL;
Variable * TimedMachine::SYSTEM_VAR_DELTA_TIME  = NULL;


void TimedMachine::genProperty(Machine * machine)
{
	PropertyPart & decl = machine->getPropertyPart();
	Variable * aVar;

	// TypeManager::UINTEGER/*TIME*/
	TypeSpecifier timeType( TypeManager::newClockTime(
			TYPE_TIME_SPECIFIER, TypeManager::UINTEGER) );

	TypeSpecifier deltaType( TypeManager::newClockTime(
			TYPE_TIME_SPECIFIER, TypeManager::POS_INTEGER) );

	TypeSpecifier clockType( TypeManager::newClockTime(
			TYPE_CLOCK_SPECIFIER, TypeManager::UINTEGER) );

	Modifier mdfrTimed;
	// GLOBAL_TIME
	BF globalTimeVar = decl.saveOwnedVariable(
			aVar = new Variable(machine,
					mdfrTimed, timeType, VAR_ID_GLOBAL_TIME) );

	if( machine->getSpecifier().isComponentSystem() )
	{
		SYSTEM_VAR_GLOBAL_TIME = aVar;
	}


	// DELTA_TIME
	BF deltaTimeVar = decl.saveOwnedVariable(
			aVar = new Variable(machine,
					mdfrTimed.addFeatureKind(Modifier::FEATURE_UNSAFE_KIND),
					deltaType, VAR_ID_DELTA_TIME) );

	if( machine->getSpecifier().isComponentSystem() )
	{
		SYSTEM_VAR_DELTA_TIME = aVar;
	}

	// time & delta getters ;
	// clock << reset & update >> routine macro
	BehavioralPart * moe = machine->getUniqBehaviorPart();

	Modifier mdfrParam(
			Modifier::NATURE_PARAMETER_KIND,
			Modifier::FEATURE_TRANSIENT_KIND );

	Variable * param;

	// time getter routine macro
	Routine * timeGetter = Routine::newDefine(*moe, ROUTINE_ID_TIME_GET);
	timeGetter->getwModifier().setNatureMacro(true);
	moe->saveRoutine( timeGetter );

	param = new Variable(timeGetter, mdfrParam, timeType, "_time_");
	timeGetter->saveReturn(param);
	timeGetter->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_RETURN, globalTimeVar ) );

	// time getter routine macro
	Routine * deltaGetter = Routine::newDefine(*moe, ROUTINE_ID_DELTA_GET);
	deltaGetter->getwModifier().setNatureMacro(true);
	moe->saveRoutine( deltaGetter );

	param = new Variable(deltaGetter, mdfrParam, deltaType, "_delta_");
	deltaGetter->saveReturn(param);
	deltaGetter->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_RETURN, deltaTimeVar ) );


	// global time << reset >> routine macro
	Routine * timeReset = Routine::newDefine(*moe, ROUTINE_ID_TIME_RESET);
	timeReset->getwModifier().setNatureMacro(true);
	moe->saveRoutine( timeReset );

	timeReset->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, globalTimeVar,
			ExpressionConstant::INTEGER_ZERO ) );


	// clock << reset >> routine macro
	Routine * clockReset = Routine::newDefine(*moe, ROUTINE_ID_CLOCK_RESET);
	clockReset->getwModifier().setNatureMacro(true);
	moe->saveRoutine( clockReset );

	param = new Variable(clockReset, mdfrParam, clockType, "_clock_");
	clockReset->saveParameter( param );
	clockReset->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, INCR_BF(param),
			ExpressionConstant::INTEGER_ZERO ) );


	// clock << update >> routine macro
	Routine * clockUpdate = Routine::newDefine(*moe, ROUTINE_ID_CLOCK_UPDATE);
	clockUpdate->getwModifier().setNatureMacro(true);
	moe->saveRoutine( clockUpdate );

	param = new Variable(clockUpdate, mdfrParam, clockType, "_clock_");
	clockUpdate->saveParameter( param );
	clockUpdate->setCode( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, INCR_BF(param),
			ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_PLUS,
					INCR_BF(param), INCR_BF(aVar)) ) );
}



void TimedMachine::genBehavior(Machine * machine)
{
	TimedMachine::genBehaviorInit(machine);

	TimedMachine::genBehaviorIRun(machine);
}


void TimedMachine::genBehaviorInit(Machine * machine)
{
	BFCode initCurrentTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN,
			machine->getPropertyPart().
					getVariables().getByNameID(VAR_ID_GLOBAL_TIME),
			TypeManager::UINTEGER/*TIME*/.getDefaultValue()/*TIME*/);

	BFCode initDeltaTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN,
			machine->getPropertyPart().
					getVariables().getByNameID(VAR_ID_DELTA_TIME),
			TypeManager::UINTEGER/*TIME*/.getDefaultValue());

	machine->getUniqBehaviorPart()->setOnInit(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
							initCurrentTime, initDeltaTime),
					machine->getUniqBehaviorPart()->getOnInit()) );
}


void TimedMachine::genBehaviorIRun(Machine * machine)
{
	BF varDeltaTime = machine->getPropertyPart().
			getVariables().getByNameID(VAR_ID_DELTA_TIME);

	BFCode newfreshDeltaTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN_NEWFRESH, varDeltaTime );

// Problème de scalabilite: passage à l'echelle ? est-ce utile ?
//	BFCode guardDeltaTime = StatementConstructor::newCode(
//			OperatorManager::OPERATOR_TIMED_GUARD,
//					ExpressionConstructor::newCode(
//						OperatorManager::OPERATOR_GT,
//						varDeltaTime, ExpressionConstant::INTEGER_ZERO) );

// Problème de scalabilite: passage à l'echelle ? est-ce utile ?
//	BF varCurrentTime = machine->getPropertyPart().
//			getVariables().getByNameID(VAR_ID_GLOBAL_TIME);
//
//	BFCode incrCurrentTime = StatementConstructor::newCode(
//			OperatorManager::OPERATOR_ASSIGN, varCurrentTime,
//			ExpressionConstructor::newCode(
//					OperatorManager::OPERATOR_PLUS,
//					varCurrentTime, varDeltaTime) );


	BFCode updateTimeClock = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
			newfreshDeltaTime/*, guardDeltaTime, incrCurrentTime*/);

	updateClock(machine, machine, varDeltaTime, updateTimeClock);

	machine->getUniqBehaviorPart()->setOnIRun(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE, updateTimeClock,
					machine->getUniqBehaviorPart()->getOnIRun()) );
}


void TimedMachine::updateClock(const Machine * modelMachine,
		Machine * aMachine, const BF & varDeltaTime,
		const BFCode & seqCode, const std::string & aQualifiedNameID)
{
	std::string aRelativeNameID = aQualifiedNameID.empty()
				? aMachine->getFullyQualifiedNameID()
				: (aQualifiedNameID + "." + aMachine->getNameID());

	updateClock(aMachine, modelMachine->getPropertyPart().getVariables(),
			varDeltaTime, seqCode, aRelativeNameID);

	CompositePart::const_machine_iterator itMachine =
			modelMachine->getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			modelMachine->getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (itMachine)->getSpecifier().isDesignPrototypeStatic() )
		{
			modelMachine = (itMachine);

		}
		else if( (itMachine)->getSpecifier().isDesignInstanceStatic() )
		{
			modelMachine = (itMachine)->getModelMachine();
		}
		else
		{
			modelMachine = NULL;
		}

		if( (modelMachine != NULL)
			&& (not modelMachine->getSpecifier().hasFeatureTimed())
			&& (modelMachine->getPropertyPart().hasVariable()
				|| modelMachine->hasMachine()) )
		{
			updateClock(modelMachine, (itMachine),
					varDeltaTime, seqCode, aRelativeNameID);
		}
	}
}

void TimedMachine::updateClock(Machine * machine,
		const TableOfVariable & variables, const BF & varDeltaTime,
		const BFCode & seqCode, const std::string & aQualifiedNameID)
{
	BF varInstance;

	TableOfVariable::const_raw_iterator itVar = variables.begin();
	TableOfVariable::const_raw_iterator endvar = variables.end();
	for( ; itVar != endvar ; ++itVar )
	{
		if( (itVar)->hasTypeSpecifier() &&
			(itVar)->getTypeSpecifier()->isTypedClock() )
		{
			if( not (itVar)->getModifier().hasModifierPublicVolatile() )
			{
				(itVar)->getwModifier().setModifierPublicVolatile();
			}

			if( not (itVar)->hasValue() )
			{
				(itVar)->setValue(ExpressionConstant::INTEGER_ZERO);
			}

			if( (machine == (itVar)->getContainerMachine())
				&& (machine->getFullyQualifiedNameID() == aQualifiedNameID) )
			{
				varInstance = (*itVar);
			}
			else
			{
				varInstance = ExpressionConstructor::newQualifiedIdentifier(
						aQualifiedNameID + "." + (itVar)->getNameID() );
			}

			BFCode updateCode(OperatorManager::OPERATOR_IF,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_STATUS_IS,
							INCR_BF(OperatorManager::OPERATOR_SCHEDULE_INVOKE),
							ExpressionConstructor::newQualifiedIdentifier(
									aQualifiedNameID) ) );


			Routine * updateClock =
					machine->rawsemRoutineByNameID(ROUTINE_ID_CLOCK_UPDATE);
			if( updateClock != NULL )
			{
//				AVM_OS_COUT << EMPHASIS("ROUTINE_ID_CLOCK_UPDATE", '*', 42);
				updateClock = Routine::newInvoke(machine, INCR_BF(updateClock));
				updateClock->appendParameter( varInstance );

				updateCode->append(ParserUtil::invokeRoutineStatement(updateClock));
			}
			else
			{
				updateCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ASSIGN, varInstance,
						ExpressionConstructor::newCode(
								OperatorManager::OPERATOR_PLUS,
								varInstance, varDeltaTime) ) );
			}

			seqCode->append( updateCode );
		}
	}
}


} /* namespace sep */
