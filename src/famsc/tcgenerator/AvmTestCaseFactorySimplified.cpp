/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmTestCaseFactory.h"
#include "AvmOutputNormalizer.h"
#include "AvmTestCaseStatistics.h"
#include "AvmTestCaseUtils.h"

#include <collection/BFContainer.h>

#include <computer/BaseEnvironment.h>
#include <computer/EvaluationEnvironment.h>

#include <famcore/api/AbstractProcessorUnit.h>
#include <famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.h>

#include <fml/builtin/Identifier.h>

#include <fml/common/ModifierElement.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/expression/StatementFactory.h>

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/Transition.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Variable.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <fml/template/TimedMachine.h>

#include <fml/type/TypeManager.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>
#include <solver/Z3Solver.h>

#include <util/ExecutionChrono.h>


namespace sep
{



Machine * AvmTestCaseFactory::buildStepSimplified(Machine & tcSourceState,
		const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC)
{
	Machine * tcTargetState = nullptr;

	Port::Table unexpectedOutputSUT( mOutputPortSUT_toInputTC );
	Port::Table uncontrollableSUT( mUncontrollableSUT_toInputTC );

	// Test purpose EC
	const BF & ioTrace = tcTargetEC.getIOElementTrace();
	const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
	const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

	if( StatementTypeChecker::isOutput(comTrace) )
	{
		if( tcTargetEC.hasChildContext() )
		{
			tcTargetState = applyRule_R02_Progress_SpecifiedOutput_Simplified(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);
		}
		else
		{
			tcTargetState = applyRule_R04_Pass_SpecifiedOutput_Simplified(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);
		}
	}
	// if( StatementTypeChecker::isInput(comTrace) )
	else if( mUncontrollableTraceFilter.pass(comPort) )
	{
// !@! DEVIATION PAUSE
		if( uncontrollableSUT.getByNameID(comPort.getNameID()).valid() )
		{
			tcTargetState = applyRule_R03_Progress_UncontrollableInput_Specified_Simplified(
					tcSourceState, tcSourceEC, comTrace, tcTargetEC);

//			uncontrollableSUT.removeByNameID(comPort.getNameID());
		}
	}
	else
	{
		tcTargetState = applyRule_R01_Progress_Stimulation_Simplified(
				tcSourceState, tcSourceEC, comTrace, tcTargetEC);
	}

	/////////////////////////////////////
	// Sibling test purpose EC
	// applyRule_R06_Inconclusive_SpecifiedOutput
	// applyRule_R07_Inconclusive_UncontrollableInput_Specified
	//
	for( const auto & aChildEC : tcSourceEC.getChildContexts()  )
	{
		if( aChildEC == (& tcTargetEC) )
		{
			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Build sibling-transition for child EC : " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		if( (not aChildEC->hasIOElementTrace())
			|| (not aChildEC->hasRunnableElementTrace() ) )
		{
			continue;
		}
		const BF & ioTrace = aChildEC->getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

		if( StatementTypeChecker::isOutput(comTrace) )
		{
			applyRule_R06_Inconclusive_SpecifiedOutput_Simplified(
					tcSourceState, tcSourceEC, comTrace, *aChildEC);
		}
		// if( StatementTypeChecker::isInput(comTrace) )
		else if( mUncontrollableTraceFilter.pass(comPort) )
		{
			applyRule_R07_Inconclusive_UncontrollableInput_Specified_Simplified(
					tcSourceState, tcSourceEC, comTrace, *aChildEC);
		}
	}



	/////////////////////////////////////
	// Sibling test purpose EC
	// applyRule_R10a_Fail_UnspecifiedOutput

// !@! DEVIATION PAUSE
	if( unexpectedOutputSUT.getByNameID(comPort.getNameID()).valid() )
	{
		applyRule_R10a_Fail_UnspecifiedOutput_Simplified(
				tcSourceState, tcSourceEC, comTrace, tcTargetEC);

		unexpectedOutputSUT.removeByNameID(comPort.getNameID());
	}

	for( const auto & aChildEC : tcSourceEC.getChildContexts()  )
	{
		if( aChildEC == (& tcTargetEC) )
		{
			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Build sibling-transition for child EC : " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		if( (not aChildEC->hasIOElementTrace())
			|| (not aChildEC->hasRunnableElementTrace() ) )
		{
			continue;
		}
		const BF & ioTrace = aChildEC->getIOElementTrace();
		const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
		const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

		if( StatementTypeChecker::isOutput(comTrace) )
		{
			if( unexpectedOutputSUT.getByNameID(comPort.getNameID()).valid() )
			{
				applyRule_R10a_Fail_UnspecifiedOutput_Simplified(
						tcSourceState, tcSourceEC, comTrace, *aChildEC);

				unexpectedOutputSUT.removeByNameID(comPort.getNameID());
			}
		}
	}

	/////////////////////////////////////
	// applyRule_R08_Inconclusive_UncontrollableInput_unspecified
	for( const auto & ucInPort : uncontrollableSUT )
	{
		applyRule_R08_Inconclusive_UncontrollableInput_unspecified_Simplified(
				tcSourceState, tcSourceEC, ucInPort, tcTargetEC);
	}

	/////////////////////////////////////
	// applyRule_R10b_Fail_UnspecifiedOutput
	for( const auto & obsPort : unexpectedOutputSUT )
	{
		applyRule_R10b_Fail_UnspecifiedOutput_Simplified(
				tcSourceState, tcSourceEC, obsPort, tcTargetEC);
	}

// !@! DEVIATION PAUSE
	// Quiescence : Admissible
	applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible_Simplified(
			tcSourceState, tcSourceEC, tcTargetEC);

	// Quiescence : Unspecified
	applyRule_R11_Fail_UnspecifiedQuiescence_Simplified(
			tcSourceState, tcSourceEC, tcTargetEC);

	return tcTargetState;
}

////////////////////////////////////////////////////////////////////////////////
// RULES FOR TESCASE GENERATION
////////////////////////////////////////////////////////////////////////////////

//static void print_guard_map(const std::string message, const std::map<std::uint32_t, BF> & guardsMap)
//{
//	AVM_OS_DEBUG << "mExecutionContextIdGuardMap --> " << message << " :>" << std::endl;
//	for (const auto& [key, value] : guardsMap)
//	{
//		AVM_OS_DEBUG << '[' << key << "] = " << value.str() << std::endl;
//	}
//}

BF AvmTestCaseFactory::getPathCondition_Simplified(const ExecutionContext & anEC, bool & isnotfound)
{
	auto foundIt = mExecutionContextIdGuardMap.find(anEC.getIdNumber());
	if( foundIt != mExecutionContextIdGuardMap.end() )
	{
		isnotfound = false;
		return foundIt->second;
	}
	return anEC.getAllPathCondition();
}

void  AvmTestCaseFactory::mapExecutionContextGuard_Simplified(const ExecutionContext & anEC, const BF & aGuard)
{
//AVM_OS_DEBUG << "mapExecutionContextGuard of " << anEC.str() << std::endl
//		<< " Guard : " << aGuard.str() << std::endl;
	mExecutionContextIdGuardMap[anEC.getIdNumber()] = aGuard;
}

//BF AvmTestCaseFactory::boundTimeOutCondition(const ExecutionContext & tcSourceEC)
//{
//	// The time elapsed value : z_i
//	const BF & varElapsedTime =
//			AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);
//
//	// Time elapsed constraint
//	return ExpressionConstructor::andExpr(
//			ExpressionConstructor::ltExpr(mVariable_TC_Clock, mVariable_TC_TM),
//			ExpressionConstructor::eqExpr(varElapsedTime, mVariable_TC_Clock) );
//}


BFCode AvmTestCaseFactory::boundTimeOutCondition_Simplified(
		const ExecutionContext & tcSourceEC)
{
	// Time elapsed constraint
	return StatementConstructor::newCode(
			OperatorManager::OPERATOR_TIMED_GUARD,
			ExpressionConstructor::ltExpr(mVariable_TC_Clock, mVariable_TC_TM) );
}

BFCode AvmTestCaseFactory::boundTimeOutCondition_Simplified(
		const ExecutionContext & tcSourceEC, const BF & guardCondition)
{
	if( not guardCondition.isEqualTrue() )
	{
		const BF & varElapsedTime =
				AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC);

		if( AvmTestCaseUtils::containseParameter(guardCondition, varElapsedTime) )
		{
			return boundTimeOutCondition(tcSourceEC);
		}
	}

	// Time elapsed constraint
	return boundTimeOutCondition_Simplified(tcSourceEC);
}

BFCode AvmTestCaseFactory::unboundTimeOutCondition_Simplified(const ExecutionContext & tcSourceEC)
{
	// Time elapsed constraint
	return StatementConstructor::newCode(
			OperatorManager::OPERATOR_TIMED_GUARD,
			ExpressionConstructor::gteExpr(mVariable_TC_Clock, mVariable_TC_TM) );
}


BF AvmTestCaseFactory::targetPathCondition_Simplified(const ExecutionContext & tcTargetEC)
{
// !@! DEBUG
//print_guard_map("targetPathCondition", mExecutionContextIdGuardMap);
	bool isnotfound = true;
	BF guardCondition = getPathCondition_Simplified(tcTargetEC, isnotfound);
	if( (not guardCondition.isEqualTrue()) and (not mNewfreshInitialVars.empty()) )
	{
		if( isnotfound )
		{
			return AvmTestCaseUtils::existsExpr(mNewfreshInitialVars,
					guardCondition, mProcessor.mEnableGuardSimplification);
		}
	}

	return guardCondition;
}


BF AvmTestCaseFactory::simplifyGuardCondition(const ExecutionContext & tcSourceEC,
		const Machine & tcSourceState, const BF & guardCondition)
{
	if( guardCondition.is< AvmCode >() )
	{
		AvmCode::OperandCollectionT guardClauses;
		ExpressionFactory::collectsClause(guardCondition.bfCode(), guardClauses);

		AvmCode::OperandCollectionT incomingClauses;
		AvmCode::OperandCollectionT newfreshClauses;

		const Machine * incomingState = & tcSourceState;
		while( incomingState->hasIncomingTransition() )
		{
			Transition * incomingTransition = incomingState->getBehaviorPart()
					->getIncomingTransitions().first().to_ptr< Transition >();

			BFCode prevGuard;
			StatementFactory::collectGuard(incomingTransition->getStatement(), prevGuard);
			if( prevGuard.valid() )
			{
				const BF & prevFormula = prevGuard->first();
				if( prevFormula.is< AvmCode >()
					&& prevFormula.to< AvmCode >().isOpCode(AVM_OPCODE_AND) )
				{
					ExpressionFactory::collectsClause(prevFormula.bfCode(), incomingClauses);
				}
				else
				{
					incomingClauses.append(prevFormula);
				}

				bool isNewfreshClause;
				for( const auto & guardClause : guardClauses )
				{
					isNewfreshClause = true;
					for( const auto & incomingClause : incomingClauses )
					{
						if( guardClause.isEQ(incomingClause) )
						{
							isNewfreshClause = false;
							break;
						}
					}
					if( isNewfreshClause )
					{
						newfreshClauses.append(guardClause);
					}
				}

				guardClauses.clear();
				guardClauses.splice(newfreshClauses);
			}
			incomingState = &(incomingTransition->getSource());
		}
		if( guardClauses.empty() )
		{
			return ExpressionConstant::BOOLEAN_TRUE;
		}
		else
		{
			std::vector<BF> newfreshParamsAtHeight;
			Variable::Table varInputArgs;
			AvmTestCaseUtils::newfreshInoutVarsFromEC(tcSourceEC, *mMachineTC, varInputArgs);
			newfreshParamsAtHeight.insert(newfreshParamsAtHeight.end(),
					varInputArgs.begin(), varInputArgs.end() );
			newfreshParamsAtHeight.push_back(
					AvmTestCaseUtils::newfreshDurationVarFromEC(tcSourceEC, *mMachineTC) );

			if( not AvmTestCaseUtils::containsSomeParameter(guardClauses, newfreshParamsAtHeight) )
			{
				return ExpressionConstant::BOOLEAN_TRUE;
			}
			else
			{
				return ExpressionConstructor::andExpr(guardClauses);
			}
		}
	}

	return guardCondition;
}


static BF nodeConditionsFromHeight(
		const ExecutionContext::VectorOfConstPtr & testPurposeTrace, std::size_t height)
{
	AvmCode::OperandCollectionT nodeConditions;
	std::size_t heightMax = testPurposeTrace.size();
	for( std::size_t offset = height ; offset < heightMax ; offset++ )
	{
		nodeConditions.push_back( testPurposeTrace[offset]->getAllNodeCondition() );
	}
	return ExpressionConstructor::andExpr(nodeConditions);
}

//static const std::string STATE_NAME_PASS            = "PASS";
//static const std::string STATE_NAME_FAIL_OUT        = "FAIL^out";
//static const std::string STATE_NAME_FAIL_DUR        = "FAIL^dur";
//static const std::string STATE_NAME_INC_OUT         = "INC^out";
//static const std::string STATE_NAME_INC_DUR         = "INC^dur";
//static const std::string STATE_NAME_INC_UC_IN_SPEC  = "INC^ucIn_spec";
//static const std::string STATE_NAME_INC_UC_IN_USPEC = "INC^ucIn_uspec";

static const std::string STATE_NAME_PASS            = "PASS";
static const std::string STATE_NAME_FAIL_OUT        = "FAILout";
static const std::string STATE_NAME_FAIL_DUR        = "FAILdur";
static const std::string STATE_NAME_INC_OUT         = "INCout";
static const std::string STATE_NAME_INC_DUR         = "INCdur";
static const std::string STATE_NAME_INC_UC_IN_SPEC  = "INCucInSpec";
static const std::string STATE_NAME_INC_UC_IN_USPEC = "INCucInUspec";

//static const std::string STATE_NAME_PASS            = "Pass";
//static const std::string STATE_NAME_FAIL_OUT        = "FailOut";
//static const std::string STATE_NAME_FAIL_DUR        = "FailDur";
//static const std::string STATE_NAME_INC_OUT         = "IncOut";
//static const std::string STATE_NAME_INC_DUR         = "IncDur";
//static const std::string STATE_NAME_INC_UC_IN_SPEC  = "IncUcInSpec";
//static const std::string STATE_NAME_INC_UC_IN_USPEC = "IncUcInUspec";

// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R01_Progress_Stimulation_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R01_Progress_Stimulation for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\ttp_PC : " << mTestPurposePathCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber());

	std::string stateName = (OSS() << "ec" << tcTargetEC.getIdNumber());
//		<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));

	Machine * tcTargetState = Machine::newState(mMachineTC,
		stateID, Specifier::STATE_SIMPLE_MOC, stateName);

	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + stateName + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The guard
	BF guardCondition = ExpressionConstant::BOOLEAN_TRUE;
	if( not mTestPurposePathCondition.isEqualTrue() )
	{
		Variable::Table boundVars( mNewfreshInitialTraceVarsTP );

		Variable::Table newfreshTraceVarsTargetEC;
		AvmTestCaseUtils::newfreshTraceVarsFromEC(
				tcSourceEC, *mMachineTC, newfreshTraceVarsTargetEC);

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSING )
		newfreshTraceVarsTargetEC.strFQN( AVM_OS_DEBUG << "newfreshVarsTargetEC :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSING )

//		existsBoundVars.remove(F_vars(TargetEC));
		for( const auto & freshVarTargetEC : newfreshTraceVarsTargetEC )
		{
			boundVars.remove(freshVarTargetEC);
		}

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSING )
	boundVars.strFQN( AVM_OS_DEBUG << "existsBoundVars :" << std::endl );
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSING )

//				guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
//						ExpressionConstructor::andExpr(
//								guardCondition,
//								boundVars.empty()
//									? mTestPurposePathCondition
//									: AvmTestCaseUtils::existsExpr(boundVars,
//											mTestPurposePathCondition,
//											mProcessor.mEnableGuardSimplification)));

				BF nodeConditionsFromNextHeight = nodeConditionsFromHeight(
						mTestPurposeTrace, tcTargetEC.getHeight());

				guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
						ExpressionConstructor::andExpr(
								tcTargetEC.getAllPathCondition(),
								boundVars.empty()
									? nodeConditionsFromNextHeight
									: AvmTestCaseUtils::existsExpr(boundVars,
											nodeConditionsFromNextHeight,
											mProcessor.mEnableGuardSimplification)));
	}

	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	// The Stimulation com statement
	BFCode tcStimulationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcStimulationComStatement, tcClockReset));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC, guardCondition);

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, guard, tcStimulationComStatement, tcClockReset));
	}

	return tcTargetState;
}

// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R02_Progress_SpecifiedOutput_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R02_Progress_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC    : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber());

	std::string stateName = (OSS() << "ec" << tcTargetEC.getIdNumber());
//		<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));

	Machine * tcTargetState = Machine::newState(mMachineTC,
		stateID, Specifier::STATE_SIMPLE_MOC, stateName);

	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + stateName + "_"  + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));
	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(*(tcTargetEC.getContainer()));

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, tcClockReset));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition(*(tcTargetEC.getContainer()));

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard, tcClockReset));	}

	return tcTargetState;
}

// PROGRESS
Machine * AvmTestCaseFactory::applyRule_R03_Progress_UncontrollableInput_Specified_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R03_Progress_UncontrollableInput_Specified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state on the test purpose path
	std::string stateID = (OSS() << "ec_" << tcTargetEC.getIdNumber());

	std::string stateName = (OSS() << "ec" << tcTargetEC.getIdNumber());
//		<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));

	Machine * tcTargetState = Machine::newState(mMachineTC,
		stateID, Specifier::STATE_SIMPLE_MOC, stateName);

	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + stateName + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));
	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	// The reset of the testcase clock
	BFCode tcClockReset = StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN, mVariable_TC_Clock,
			ExpressionConstant::INTEGER_ZERO);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(*(tcTargetEC.getContainer()));

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, tcClockReset));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition(*(tcTargetEC.getContainer()));

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard, tcClockReset));
	}

	return tcTargetState;
}

// PROGRESS --> PASS
Machine * AvmTestCaseFactory::applyRule_R04_Pass_SpecifiedOutput_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R04_Pass_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state PASS of the test purpose
	Machine * tcTargetState = mStateTC_PASS;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber());

//		std::string stateName = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber()
//			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));

		tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_FINAL_MOC, STATE_NAME_PASS); //stateName);
	}

	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition PASS of the test purpose
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_PASS + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));
	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(*(tcTargetEC.getContainer()));

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition(*(tcTargetEC.getContainer()));

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}

	return tcTargetState;
}

Machine * AvmTestCaseFactory::applyRule_R05_Pass_SpecifiedQuiescence_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R05_Pass_SpecifiedQuiescence for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The target state PASS of the test purpose
	Machine * tcTargetState = mStateTC_PASS;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber());

//		std::string stateName = (OSS() << "PASS_ec_" << tcTargetEC.getIdNumber()
//			<< "_" << tcTargetEC.getExecutionData().strStateConf("%4%"));

		tcTargetState = Machine::newState(mMachineTC,
			stateID, Specifier::STATE_FINAL_MOC, STATE_NAME_PASS); //stateName);
	}

	mMachineTC->saveOwnedElement(tcTargetState);

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The transition PASS of the test purpose
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_PASS + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));
	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = unboundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = unboundTimeOutCondition(tcSourceEC);

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}

	return tcTargetState;
}


// INCONCLUSIVE OUTPUT
void AvmTestCaseFactory::applyRule_R06_Inconclusive_SpecifiedOutput_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R06_Inconclusive_SpecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));

	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	if( guardCondition.isEqualFalse() )
	{
		return;
	}

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_INC_OUT;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "INC_out_ec_" << tcSourceEC.getIdNumber()
				<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
		tcTargetState = Machine::newState(mMachineTC, stateID,
				Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_INC_OUT);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_INC_OUT + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(*(tcTargetEC.getContainer()));

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition(*(tcTargetEC.getContainer()));

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}
}

// INCONCLUSIVE UNCONTROLLABLE INPUT SPECIFIED
void AvmTestCaseFactory::applyRule_R07_Inconclusive_UncontrollableInput_Specified_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R07_Inconclusive_UncontrollableInput_Specified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			targetPathCondition_Simplified(tcTargetEC));

	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	if( guardCondition.isEqualFalse() )
	{
		return;
	}

	const std::string & portID =
			comTrace->first().to< InstanceOfPort >().getNameID();

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_INC_UC_IN_SPEC;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "INC_ucInSpec_ec_" << tcSourceEC.getIdNumber()
				<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
		tcTargetState = Machine::newState(mMachineTC, stateID,
				Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_INC_UC_IN_SPEC);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_INC_UC_IN_USPEC + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	if( guardCondition.isEqualTrue() )
	{
		// The timed guard
		BFCode timedGuard = boundTimeOutCondition_Simplified(*(tcTargetEC.getContainer()));

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		// The timed guard
		BFCode timedGuard = boundTimeOutCondition(*(tcTargetEC.getContainer()));

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}
}

// INCONCLUSIVE UNCONTROLLABLE INPUT UNSPECIFIED
void AvmTestCaseFactory::applyRule_R08_Inconclusive_UncontrollableInput_unspecified_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BF & ucInPort, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R08_Inconclusive_UncontrollableInput_unspecified for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tucInPort : " << ucInPort.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const Port & ucInPortTC = ucInPort.to< Port >();

	// The guard
	BFCode ucontrollableInputGuards = ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isInput(specComTrace) )
			{
				const InstanceOfPort & ucinSpecPort =
						specComTrace->first().to< InstanceOfPort >();
				if( ucInPortTC.getNameID() == ucinSpecPort.getNameID() )
				{
					ucontrollableInputGuards.append(
							ExpressionConstructor::notExpr(
									targetPathCondition_Simplified(*aChildEC) ) );

//					if( aChildEC->getAllPathCondition().isEqualTrue() )
//					{
//						return;
//					}
				}
			}
		}
	}

	// The guard
	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			( ucontrollableInputGuards.size() > 1 )
				? ucontrollableInputGuards
				: ( ucontrollableInputGuards.size() > 0 )
					? ucontrollableInputGuards->first()
					: ExpressionConstant::BOOLEAN_TRUE);

//	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	if( guardCondition.isEqualFalse() )
	{
		return;
	}

	const std::string & portID = ucInPortTC.getNameID();

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_INC_UC_IN_USPEC;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "INC_ucInUspec_ec_"
				<< tcSourceEC.getIdNumber() << "_" << portID);
		tcTargetState = mMachineTC->getMachineByNameID(stateID);
		if( tcTargetState == nullptr )
		{
			tcTargetState = Machine::newState(mMachineTC, stateID,
					Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_INC_UC_IN_USPEC);
			mMachineTC->saveOwnedElement(tcTargetState);
		}
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_INC_UC_IN_USPEC + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Observation com statement
	BFCode tcObservationComStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, ucInPort);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC, guardCondition);

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}
}


// INCONCLUSIVE SPECIFIED QUIESCENCE ADMISSIBLE
void AvmTestCaseFactory::applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			compute_R09_QuiescenceCondition_Simplified(tcSourceEC, tcSourceState));

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

//	mapExecutionContextGuard_Simplified(tcTargetEC, quiescenceCondition);

	if( quiescenceCondition.isEqualFalse() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition is FALSE ! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		return;
	}

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_INC_DUR;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "INC_dur_ec_" << tcSourceEC.getIdNumber() );
		tcTargetState = Machine::newState(mMachineTC, stateID,
				Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_INC_DUR);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_INC_DUR + "_Quiescence", Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Quiescence Observation com statement
	BFCode failQuiescenceStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, mQuiescencePortTC);

	//	mapExecutionContextGuard_Simplified(tcTargetEC, quiescenceCondition);
	if( quiescenceCondition.isEqualTrue() )
	{
		BFCode timedGuard = unboundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, failQuiescenceStatement));
	}
	else 
	{
		BFCode timedGuard = unboundTimeOutCondition(tcSourceEC);

		// Statistic collector
		mTestCaseStatistics.takeAccount(quiescenceCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, quiescenceCondition);
	
		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, failQuiescenceStatement, guard));
	}
}

BF AvmTestCaseFactory::compute_R09_QuiescenceCondition_Simplified(
		const ExecutionContext & tcSourceEC, const Machine & tcSourceState)
{
	AvmCode::OperandCollectionT phiQuiescence;

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();
			if( comPort.isTEQ(mQuiescencePortTP.rawPort()) )
			{
				if( not aChildEC->getAllPathCondition().isEqualTrue() )
				{
					BF quiescenceCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
							AvmTestCaseUtils::existsExpr(mNewfreshInitialVars,
									aChildEC->getAllPathCondition(),
									mProcessor.mEnableGuardSimplification
							)
					);
					mapExecutionContextGuard_Simplified(*aChildEC, quiescenceCondition);

					phiQuiescence.append(quiescenceCondition);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R9_Quiescence condition for output< " << comPort.getNameID()
		<< " > of " << aChildEC->str() << " : ";
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
				}
			}
		}
	}

	if( phiQuiescence.nonempty() )
	{
		return ExpressionConstructor::orExpr(phiQuiescence);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


// FAIL UNSPECIFIED OUTPUT
void AvmTestCaseFactory::applyRule_R10a_Fail_UnspecifiedOutput_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R10a_Fail_UnspecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tTrace : " << comTrace.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const InstanceOfPort & failOutPort = comTrace->first().to< InstanceOfPort >();

	// The guard
	BFCode outputGuards = StatementConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isOutput(specComTrace) )
			{
				const InstanceOfPort & specOutPort =
						specComTrace->first().to< InstanceOfPort >();
				if( (& failOutPort) == (& specOutPort) )
				{
					outputGuards.append(
							ExpressionConstructor::notExpr(
									targetPathCondition_Simplified(*aChildEC) ) );
//					outputGuards.append(
//							StatementConstructor::newCode(
//									OperatorManager::OPERATOR_NOT,
//									targetPathCondition_Simplified(*aChildEC) ) );

//					if( aChildEC->getAllPathCondition().isEqualTrue() )
//					{
//						return;
//					}
				}
			}
		}
	}

	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			( outputGuards.size() > 1 )
				? outputGuards
				: ( outputGuards.size() > 0 )
					? outputGuards->first()
					: ExpressionConstant::BOOLEAN_TRUE);

//	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	if( guardCondition.isEqualFalse() )
	{
		return;
	}

	const std::string & portID = failOutPort.getNameID();

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_FAIL_OUT;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS()<< "FAIL_out_ec_" << tcSourceEC.getIdNumber()
				<< "_" << tcTargetEC.getIdNumber() << "_" << portID);
		tcTargetState = mMachineTC->getMachineByNameID(stateID);
		if( tcTargetState == nullptr )
		{
			tcTargetState = Machine::newState(mMachineTC, stateID,
					Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_FAIL_OUT);
			mMachineTC->saveOwnedElement(tcTargetState);
		}
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_FAIL_OUT + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Observation com statement
	BFCode tcObservationComStatement =
			AvmTestCaseUtils::tpTrace_to_tcStatement(*mMachineTC, comTrace);

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC, guardCondition);

		// Statistic collector
		mTestCaseStatistics.takeAccount(guardCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}
}


// FAIL UNSPECIFIED OUTPUT
void AvmTestCaseFactory::applyRule_R10b_Fail_UnspecifiedOutput_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BF & obsPort, const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R10b_Fail_UnspecifiedOutput for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tobsPort : " << obsPort.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	const Port & inputPortTC = obsPort.to< Port >();

	// The guard
	BFCode unspecifiedOutputGuards = StatementConstructor::newCode(
			OperatorManager::OPERATOR_AND );
	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
		if( aChildEC->hasIOElementTrace() && aChildEC->hasRunnableElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & specComTrace = BaseEnvironment::searchTraceIO(ioTrace);

			if( StatementTypeChecker::isInput(specComTrace) )
			{
				const InstanceOfPort & ucinSpecPort =
						specComTrace->first().to< InstanceOfPort >();
				if( inputPortTC.getNameID() == ucinSpecPort.getNameID() )
				{
					unspecifiedOutputGuards.append(
							ExpressionConstructor::notExpr(
									targetPathCondition_Simplified(*aChildEC) ) );

//					if( aChildEC->getAllPathCondition().isEqualTrue() )
//					{
//						return;
//					}
				}
			}
		}
	}

	BF guardCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			( unspecifiedOutputGuards.size() > 1 )
				? unspecifiedOutputGuards
				: ( unspecifiedOutputGuards.size() > 0 )
					? unspecifiedOutputGuards->first()
					: ExpressionConstant::BOOLEAN_TRUE);

//	mapExecutionContextGuard_Simplified(tcTargetEC, guardCondition);

	if( guardCondition.isEqualFalse() )
	{
		return;
	}

	const std::string & portID = inputPortTC.getNameID();

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_FAIL_OUT;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS()<< "FAIL_out_ec_" << tcSourceEC.getIdNumber()
				<< "_" << portID);
		tcTargetState = mMachineTC->getMachineByNameID(stateID);
		if( tcTargetState == nullptr )
		{
			tcTargetState = Machine::newState(mMachineTC, stateID,
					Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_FAIL_OUT);
			mMachineTC->saveOwnedElement(tcTargetState);
		}
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_FAIL_OUT + "_" + portID, Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Observation com statement
	BFCode tcObservationComStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, obsPort);
	std::vector<BF> mewfreshParams;
	if( mOutputNormalizer.getOutportParameters(
			tcSourceEC.getHeight() + 1, portID, mewfreshParams) )
	{
		for( const auto & param : mewfreshParams )
		{
			const std::string & varArgID = param.to< InstanceOfData >().getNameID();
			const BF & varArg = mMachineTC->getVariable(varArgID);
			if( varArg.valid() )
			{
				tcObservationComStatement.append(varArg);
			}
		}
	}
	else
	{
		for( const auto & paramDecl : inputPortTC.getParameters() )
		{
			const BF & paramPort = mMachineTC->getPropertyPart().saveOwnedElement(
					new Variable(mMachineTC, Modifier::PROPERTY_PRIVATE_MODIFIER,
							paramDecl.to< Variable >().getType(),
							mOutputNormalizer.newFreshOutportParameter()) );
			tcObservationComStatement.append(paramPort);
		}
	}

	if( guardCondition.isEqualTrue() )
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement));
	}
	else
	{
		BFCode timedGuard = boundTimeOutCondition_Simplified(tcSourceEC, guardCondition);

		// Statistic collector
		mTestCaseStatistics.takeAccount(unspecifiedOutputGuards, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, guardCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, tcObservationComStatement, guard));
	}
}

// FAIL DURATION : UNSPECIFIED QUIESCENCE
void AvmTestCaseFactory::applyRule_R11_Fail_UnspecifiedQuiescence_Simplified(
		Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const ExecutionContext & tcTargetEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << std::endl << EMPHASIS( "applyRule_R11_Fail_UnspecifiedQuiescence for " )
		<< "\tSource EC : " << tcSourceEC.str() << std::endl
		<< "\tTarget EC : " << tcTargetEC.str() << std::endl
		<< "\tPC   : " << tcTargetEC.getAllPathCondition().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

	BF quiescenceCondition = simplifyGuardCondition(tcSourceEC, tcSourceState,
			compute_R11_QuiescenceCondition_Simplified(tcSourceEC));

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition " << quiescenceCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

//	mapExecutionContextGuard_Simplified(tcTargetEC, quiescenceCondition);

	if( quiescenceCondition.isEqualFalse() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )
	AVM_OS_DEBUG << "Quiescence condition is FALSE ! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSING )

		return;
	}

	// The target state on the test purpose path
	Machine * tcTargetState = mStateTC_FAIL_DUR;
	if( not mProcessor.mEnableGlobalVerdictState )
	{
		std::string stateID = (OSS() << "FAIL_dur_ec_" << tcSourceEC.getIdNumber() );
		tcTargetState = Machine::newState(mMachineTC, stateID,
				Specifier::PSEUDOSTATE_TERMINAL_MOC, STATE_NAME_FAIL_DUR);
		mMachineTC->saveOwnedElement(tcTargetState);
	}

	// The transition on the test purpose path
	Transition * tpTransition = new Transition(tcSourceState,
			"tr_" + STATE_NAME_FAIL_DUR + "_Quiescence", Transition::MOC_SIMPLE_KIND);
	tpTransition->setTarget( *tcTargetState );
	const BF & bfTransition = tcSourceState.saveOwnedElement( tpTransition );
	tcTargetState->getUniqBehaviorPart()->appendIncomingTransition(bfTransition);

	// The Quiescence Observation com statement
	BFCode failQuiescenceStatement = StatementConstructor::newCode(
			OperatorManager::OPERATOR_INPUT, mQuiescencePortTC);

	if( quiescenceCondition.isEqualTrue() )
	{
		BFCode timedGuard = unboundTimeOutCondition_Simplified(tcSourceEC);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, failQuiescenceStatement));
	}
	else
	{
		BFCode timedGuard = unboundTimeOutCondition(tcSourceEC);

		// Statistic collector
		mTestCaseStatistics.takeAccount(quiescenceCondition, tpTransition);

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD, quiescenceCondition);

		tpTransition->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				timedGuard, failQuiescenceStatement, guard));
	}
}


BF AvmTestCaseFactory::compute_R11_QuiescenceCondition_Simplified(
		const ExecutionContext & tcSourceEC)
{
	AvmCode::OperandCollectionT phiQuiescence;

	for( const auto & aChildEC : tcSourceEC.getChildContexts() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for " << aChildEC->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )

		if( aChildEC->hasIOElementTrace() )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort =
					comTrace->first().to< InstanceOfPort >();

			if( comPort.isTEQ(mQuiescencePortTP.rawPort()) )
			{
				bool isnotfound = true;
				BF ChildCondition = getPathCondition_Simplified(*aChildEC, isnotfound);

				phiQuiescence.append(
						AvmTestCaseUtils::forallExpr(mNewfreshInitialVars,
								ExpressionConstructor::notExpr(ChildCondition),
								mProcessor.mEnableGuardSimplification
						)
				);
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
	AVM_OS_DEBUG << "R11_Quiescence condition for < " << comPort.getNameID() << " > of "
		<< aChildEC->str() << " : " << phiQuiescence.last().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSING , TEST_DECISION )
			}
		}
	}
	if( phiQuiescence.nonempty() )
	{
		return ExpressionConstructor::andExpr(phiQuiescence);
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}


} /* namespace sep */
