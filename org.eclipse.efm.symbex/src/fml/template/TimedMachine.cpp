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

#include <computer/PathConditionProcessor.h>

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

Variable * TimedMachine::SYSTEM_VAR_GLOBAL_TIME = nullptr;
Variable * TimedMachine::SYSTEM_VAR_DELTA_TIME  = nullptr;


avm_type_specifier_kind_t
TimedMachine::timeTypeSpecifierKind(const Specifier & specifier)
{
	if( specifier.isFeatureTimed() )
	{
		return TYPE_TIME_SPECIFIER;
	}

	else if( specifier.isFeatureContinuousTimed() )
	{
		return TYPE_CONTINUOUS_TIME_SPECIFIER;
	}
	else if( specifier.isFeatureDenseTimed() )
	{
		return TYPE_DENSE_TIME_SPECIFIER;
	}
	else //if( specifier.isFeatureDiscreteTimed() )
	{
		return TYPE_DISCRETE_TIME_SPECIFIER;
	}
}

const TypeSpecifier &
TimedMachine::timeTypeSpecifier(const Specifier & specifier)
{
	if( specifier.isFeatureTimed() )
	{
		return TypeManager::URATIONAL;
	}

	else if( specifier.isFeatureDiscreteTimed() )
	{
		return TypeManager::UINTEGER;
	}
	else if( specifier.isFeatureDenseTimed() )
	{
		return TypeManager::URATIONAL;
	}
	else // if( specifier.isFeatureContinuousTimed() )
	{
		return TypeManager::UREAL;
	}
}

void TimedMachine::genProperty(Machine & machine)
{
	PropertyPart & aPropertyPart = machine.getPropertyPart();

	avm_type_specifier_kind_t time_type_specifier =
			timeTypeSpecifierKind(machine.getSpecifier());

	TypeSpecifier timeType( TypeManager::newClockTime(time_type_specifier,
			timeTypeSpecifier(machine.getSpecifier())) );

	Variable * timeVar = aPropertyPart.addTimeSupport(timeType);

	TypeSpecifier deltaType( TypeManager::newClockTime(time_type_specifier,
			timeTypeSpecifier(machine.getSpecifier())) );

	Variable * deltaVar = aPropertyPart.addDeltaTimeSupport(deltaType);

	if( machine.getSpecifier().isComponentSystem() )
	{
		SYSTEM_VAR_GLOBAL_TIME = timeVar;
		SYSTEM_VAR_DELTA_TIME  = deltaVar;
	}

	// time & delta getters ;
	// clock << reset & update >> routine macros
	machine.getUniqBehaviorPart()->addTimeSupport( aPropertyPart );
}



void TimedMachine::genBehavior(Machine & machine)
{
	TimedMachine::genBehaviorInit(machine);

	TimedMachine::genTimeUpdate(machine);

//	TimedMachine::genBehaviorIRun(machine);
}


void TimedMachine::genBehaviorInit(Machine & machine)
{
	BFCode initCurrentTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN,
			machine.getPropertyPart().exprTimeVariable(),
			machine.getPropertyPart().exprTimeInitialConstant());

	BFCode initDeltaTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN,
			machine.getPropertyPart().exprDeltaTimeVariable(),
			machine.getPropertyPart().exprDeltaTimeInitialConstant());

	machine.getUniqBehaviorPart()->setOnInit(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
							initCurrentTime, initDeltaTime),
					machine.getUniqBehaviorPart()->getOnInit()) );
}


void TimedMachine::genBehaviorIRun(Machine & machine)
{
	BF varDeltaTime = machine.getPropertyPart().exprDeltaTimeVariable();

	BFCode newfreshDeltaTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN_NEWFRESH, varDeltaTime );

	BFCode guardDeltaTime;
// Problème de scalabilite: passage à l'echelle ?
	if( PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
	{
		guardDeltaTime = StatementConstructor::newCode(
				OperatorManager::OPERATOR_TIMED_GUARD,
						ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_GT,
							varDeltaTime, ExpressionConstant::INTEGER_ZERO) );
	}

// Problème de scalabilite: passage à l'echelle ? est-ce utile ?
	BF varCurrentTime = machine.getPropertyPart().exprTimeVariable();

	BFCode incrCurrentTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, varCurrentTime,
			ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_PLUS,
					varCurrentTime, varDeltaTime) );

	BFCode updateTimeClock = guardDeltaTime.valid()
			? StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					newfreshDeltaTime, guardDeltaTime, incrCurrentTime)
			: StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					newfreshDeltaTime, incrCurrentTime);

	updateClock(machine, machine, varDeltaTime, updateTimeClock);

	machine.getUniqBehaviorPart()->setOnIRun(
			StatementConstructor::xnewCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE, updateTimeClock,
					machine.getUniqBehaviorPart()->getOnIRun()) );
}


void TimedMachine::genTimeUpdate(Machine & machine)
{
	// time << update >> routine macro
	Routine * timeUpdate = Routine::newDefine(
			*(machine.getBehavior()), BehavioralPart::ROUTINE_ID_TIME_UPDATE);
	timeUpdate->getwModifier().setNatureMacro(true);
	machine.getBehavior()->saveRoutine( timeUpdate );


	BF varDeltaTime = machine.getPropertyPart().exprDeltaTimeVariable();

	BFCode newfreshDeltaTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN_NEWFRESH, varDeltaTime );

	BFCode guardDeltaTime;
	// Problème de scalabilite: passage à l'echelle ?
	if( PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED )
	{
		guardDeltaTime = StatementConstructor::newCode(
				OperatorManager::OPERATOR_TIMED_GUARD,
						ExpressionConstructor::newCode(
							OperatorManager::OPERATOR_GT,
							varDeltaTime, ExpressionConstant::INTEGER_ZERO) );
	}

	BF varCurrentTime = machine.getPropertyPart().exprTimeVariable();

	BFCode incrCurrentTime = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, varCurrentTime,
			ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_PLUS,
					varCurrentTime, varDeltaTime) );


	BFCode updateTimeClock = guardDeltaTime.valid()
			? StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					newfreshDeltaTime, guardDeltaTime, incrCurrentTime)
			: StatementConstructor::newCode(
					OperatorManager::OPERATOR_ATOMIC_SEQUENCE,
					newfreshDeltaTime, incrCurrentTime);

	updateClock(machine, machine, varDeltaTime, updateTimeClock);

	timeUpdate->setCode( updateTimeClock );

	// exec $ROUTINE_ID_TIME_UPDATE
	if( machine.getPropertyPart().getTimeVariable()
			->getTypeSpecifier().isTypedDiscreteTime() )
	{
		machine.getUniqBehaviorPart()->setOnIRun(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						Routine::invokeRoutineStatement(
							Routine::newInvoke(machine, INCR_BF(timeUpdate))),
						machine.getUniqBehaviorPart()->getOnIRun()) );
	}
	else
	{
		machine.getUniqBehaviorPart()->setOnRun(
				StatementConstructor::xnewCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						Routine::invokeRoutineStatement(
							Routine::newInvoke(machine, INCR_BF(timeUpdate))),
						machine.getUniqBehaviorPart()->getOnRun()) );
	}
}


void TimedMachine::updateClock(Machine & modelMachine,
		Machine & machine, const BF & varDeltaTime,
		const BFCode & seqCode, const std::string & aQualifiedNameID)
{
	std::string aRelativeNameID = aQualifiedNameID.empty()
				? machine.getFullyQualifiedNameID()
				: (aQualifiedNameID + "." + machine.getNameID());

	updateClock(machine, modelMachine.getPropertyPart().getVariables(),
			varDeltaTime, seqCode, aRelativeNameID);

	CompositePart::machine_iterator itMachine =
			modelMachine.getCompositePart()->machine_begin();
	CompositePart::machine_iterator endMachine =
			modelMachine.getCompositePart()->machine_end();
	for( Machine * pMachine = nullptr ; itMachine != endMachine ; ++itMachine )
	{
		if( (itMachine)->getSpecifier().isDesignPrototypeStatic() )
		{
			pMachine = (*itMachine).to_ptr< Machine >();

		}
		else if( (itMachine)->getSpecifier().isDesignInstanceStatic() )
		{
			pMachine = const_cast< Machine * >( (itMachine)->getModelMachine() );
		}
		else
		{
			pMachine = nullptr;
		}

		if( (pMachine != nullptr)
			&& (not pMachine->getSpecifier().hasFeatureTimed())
			&& (pMachine->getPropertyPart().hasVariable()
				|| pMachine->hasMachine()) )
		{
			updateClock((* pMachine), (itMachine),
					varDeltaTime, seqCode, aRelativeNameID);
		}
	}
}

void TimedMachine::updateClock(Machine & machine,
		const TableOfVariable & variables, const BF & varDeltaTime,
		const BFCode & seqCode, const std::string & aQualifiedNameID)
{
	BF varInstance;

	BFCode updateCode(OperatorManager::OPERATOR_ATOMIC_SEQUENCE);

	TableOfVariable::const_raw_iterator itVar = variables.begin();
	TableOfVariable::const_raw_iterator endvar = variables.end();
	for( ; itVar != endvar ; ++itVar )
	{
		std::string routineNameID;
		if( (itVar)->hasTypeSpecifier() )
		{
			const BaseTypeSpecifier & aTypeSpecifier = (itVar)->getTypeSpecifier();
			if( aTypeSpecifier.isTypedClock() )
			{
				routineNameID = BehavioralPart::ROUTINE_ID_CLOCK_UPDATE;
			}
			else if( aTypeSpecifier.hasTypeArrayVector()
					&& aTypeSpecifier.to< ContainerTypeSpecifier >()
							.getContentsTypeSpecifier().isTypedClock() )
			{
				routineNameID = BehavioralPart::ROUTINE_ID_VECTOR_CLOCK_UPDATE;
			}
		}
		else if( (itVar)->hasDataType() )
		{
			const DataType & aDataType = (itVar)->getDataType();
			if( aDataType.hasTypeArrayVector()
				&& aDataType.hasContentsTypeSpecifier() )
			{
				const BF & aType = aDataType.getContentsTypeSpecifier();

				if( aType.is< BaseTypeSpecifier >()
					&& aType.to< BaseTypeSpecifier >().isTypedClock() )
				{
					routineNameID = BehavioralPart::ROUTINE_ID_VECTOR_CLOCK_UPDATE;
				}
			}
		}

		if( not routineNameID.empty() )
		{
			if( not (itVar)->getModifier().hasModifierPublicVolatile() )
			{
				(itVar)->getwModifier().setModifierPublicVolatile();
			}

			if( not (itVar)->hasValue()
				&& (routineNameID == BehavioralPart::ROUTINE_ID_CLOCK_UPDATE) )
			{
				(itVar)->setValue(ExpressionConstant::INTEGER_ZERO);
			}

			if( machine.isTEQ( (itVar)->getContainerMachine() )
				&& (machine.getFullyQualifiedNameID() == aQualifiedNameID) )
			{
				varInstance = (*itVar);
			}
			else
			{
				varInstance = ExpressionConstructor::newQualifiedIdentifier(
						aQualifiedNameID + "." + (itVar)->getNameID() );
			}

			Routine * updateClock = machine.rawsemRoutineByNameID(routineNameID);
			if( updateClock != nullptr )
			{
				updateClock = Routine::newInvoke(machine, INCR_BF(updateClock));
				updateClock->getPropertyPart().appendVariableParameter(
						varInstance );

				updateCode->append(Routine::invokeRoutineStatement(updateClock));
			}
			else
			{
				updateCode->append( StatementConstructor::newCode(
						OperatorManager::OPERATOR_ASSIGN, varInstance,
						ExpressionConstructor::newCode(
								OperatorManager::OPERATOR_PLUS,
								varInstance, varDeltaTime) ) );
			}
		}
	}

	if( updateCode->hasOperand() )
	{
		if( machine.getSpecifier().hasFeatureTimed() )
		{
			seqCode->append(
					updateCode->hasOneOperand() ?
							updateCode->first() : updateCode );
		}
		else
		{
			seqCode->append( StatementConstructor::newCode(
					OperatorManager::OPERATOR_IF,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_STATUS_IS,
							INCR_BF(OperatorManager::OPERATOR_ENABLE_INVOKE),
							ExpressionConstructor::newQualifiedIdentifier(
									aQualifiedNameID) ),
					( updateCode->hasOneOperand() ?
							updateCode->first() : updateCode ) ) );
		}
	}
}


} /* namespace sep */
