/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 Sep. 2017
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "UnitaryTestCaseGeneratorProvider.h"

#include <computer/ExecutionDataFactory.h>
#include <computer/primitive/AvmCommunicationFactory.h>

#include <famcore/queue/ExecutionQueue.h>
#include <famsc/testing/TestCaseGenerator.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/symbol/Symbol.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Variable.h>
#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionContextFlags.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeQuery.h>
#include <fml/type/TypeManager.h>
#include <fml/trace/TraceFactory.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/CompositePart.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/Workflow.h>

#include <solver/api/SolverFactory.h>

#include <time.h>


namespace sep
{

/**
 * CONSTRUCTOR
 */
UnitaryTestCaseGeneratorProvider::UnitaryTestCaseGeneratorProvider(
		TestCaseGenerator & aTestCaseGenerator)
: AbstractTestCaseGeneratorProvider(aTestCaseGenerator),
mTPasTransitionSequence( OperatorManager::OPERATOR_SEQUENCE ),
mQUIESCENCE( OperatorManager::OPERATOR_OR ),
mCurrentTraceIndex(0),
//	mTraceChecker(this->ENV),
mTraceChecker(ENV),
mTableOfPort(),
mListOfECToErase( ),

// Test case graph
mRootGraphTestCaseEC( nullptr ),
mTestCaseEC( nullptr ),
mTestCaseChildEC( nullptr ),
mMapOfECToItsClone( ),
mRootTP( nullptr ),
mPortQuiencenceData( ),
mPortQuiencenceTime( ),
mQuiescenceRID( ),
mFailRID( ),
mINCONCRID( ),
mTestcaseSystem( ),
mStateMachine( ),
mListOfECToAddInProjection( ),
mListECToDelete ( ),
mListECUpdated ( ),
mVectorOfECAndState ( ),
mMapOfStateAndBSen ( ),
mMapOfStateAndDataVarsInst ( ),
mVectorOfPortAndRID ( ),
mListOfConnector ( ),
mListOfEnum ( ),
mListVariablesTestCase ( ),
mListECWithFlags ( ),
mIndexState ( 1 ),
mConnector ( ),
mInteractionPart ( ),
mListOfDelaysPtCTestPurpose ( ),
mListECsToResetClock ( ),
mTStart ( ),
mClockTestCase ( ),
mBoundB ( ),
mListOfTreatedECs ( ),
mINITIALSTATE ("initialstate"),
mPASSSTATE ("PASS"),
mINCONCSTATE ("INCONC"),
mFAILSTATE ("FAIL"),
mVectorOfPathConditions( )
{

}

/**
 *
 *
	UnitaryTestCaseGeneratorProvider 'Online Test Case Generation for configuration tests' {
		// required queue strategy is 'ALL'
		TPasTransitionSequence [
			// TP1
			transition = "Withdraw"
			transition = "ReturnCash"
			transition = "InsufBalance"
		] // end TPAsTransitionSequence
		IOSequence [
			// Sequence IO
			input = "Wdral"
			//output = "Cash"
			output = "Insuf"
		] // end IOSequence
		//PRESERVED [ // PRESERVED are elements that we do not want to cover
		// but we have to preserve
			//state = "FAIL"
		//] // end failState
		QUIESCENCE [ // QUIESCENCE are elements that we do want to test
		// in our model
			state = "QUIESCENCE1"
			state = "QUIESCENCE2"
		] // end quiescenceState
		projection [
			machine = "ATMBase"
			//machine = "S2"
		] // end projection
	}
 *
 *
 */

bool UnitaryTestCaseGeneratorProvider::configureImpl(const WObject * wfParameterObject)
{
	bool aConfigFlag = true;

	///////////////////////////////////////////////////////////////////////////
	const WObject * propertySequence = Query::getWSequence(
			wfParameterObject, "property");

	RuntimeQuery RQuery( getConfiguration() );

	// set RID for Quiescence state
	std::string quiescenceStateID = Query::getRegexWPropertyString(
			propertySequence, CONS_WID3("quiescence","state", "id"), "QUIESCENCE");

	mQuiescenceRID = RQuery.getRuntimeByQualifiedNameID(quiescenceStateID);

	// set RID for Fail state
	std::string failStateID = Query::getRegexWPropertyString(
			propertySequence, CONS_WID3("fail","state", "id"), "FAIL");

	mFailRID = RQuery.getRuntimeByQualifiedNameID(failStateID);

	// set RID for Inconc state
	std::string inconcStateID = Query::getRegexWPropertyString(
			propertySequence, CONS_WID3("inconc","state", "id"), "INCONC");

	mINCONCRID = RQuery.getRuntimeByQualifiedNameID(inconcStateID);

	if ( mQuiescenceRID == BF::REF_NULL || mFailRID == BF::REF_NULL )
	{
		AVM_OS_WARN << "Missing 'QUIESCENCE' or 'FAIL' state" << std::endl;
		aConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	if (aConfigFlag){

		AVM_OS_COUT << "The parameters are correctly defined for UnitaryTestCaseGeneratorProvider..." << std::endl;

	}
	else {

		AVM_OS_COUT << "The parameters are not correctly defined for UnitaryTestCaseGeneratorProvider !" << std::endl;

	}

	aConfigFlag = true;

	return aConfigFlag;
}


/**
 * preProcessing : Add transitions Fail
 */
bool UnitaryTestCaseGeneratorProvider::preprocess()
{
	AVM_OS_COUT << "PreProcess method"<< std::endl;

	return true;
}

/**
 * preFiltering
 */
bool UnitaryTestCaseGeneratorProvider::prefilter(ExecutionContext & anEC)
{
	return true;
}

void UnitaryTestCaseGeneratorProvider::getAllExecutionContextsForResetClocks(
		const BF & pathTimedConditionTestPurpose)
{
	bool newDelay = true;

	ListOfExecutionContext listOfECToReset;

	if( pathTimedConditionTestPurpose.is< AvmCode >() )
	{
		const AvmCode & formulas = pathTimedConditionTestPurpose.to< AvmCode >();

		for( const auto & operand : formulas.getOperands() )
		{
			if ( operand.is< InstanceOfData >() )
			{
				for ( const auto & delay : mListOfDelaysPtCTestPurpose )
				{
					if ( delay != operand )
					{
						newDelay = true;
					}
					else
					{
						newDelay = false;
						break;
					}
				}
				if ( newDelay )
				{
					mListOfDelaysPtCTestPurpose.append( operand );
				}
			}
			else
			{
				getAllExecutionContextsForResetClocks( operand );
			}
		}
	}
}


void UnitaryTestCaseGeneratorProvider::addQuiescenceDuetoDataInSpec(ExecutionContext * childEC,
		BF guardsDataOutputTransitions, ExecutionContext * parentEC)
{
	BF guardDataQuiescenceTransition;
	BF guardTimeQuiescenceTransition = ExpressionConstant::BOOLEAN_TRUE;

	if ( guardsDataOutputTransitions.isExpression() )
	{
		guardDataQuiescenceTransition = ExpressionConstructor::notExpr(guardsDataOutputTransitions);
	}
	else
	{
		if ( guardsDataOutputTransitions == ExpressionConstant::BOOLEAN_FALSE )
		{
			guardDataQuiescenceTransition = ExpressionConstant::BOOLEAN_TRUE;
		}
	}

	ExecutionContext * pChildECQuiescence = parentEC->cloneData(parentEC, true);

	pChildECQuiescence->getwExecutionData().setNodeTimedCondition(
			guardTimeQuiescenceTransition);

	//////////////////////////////////////////////////////////////
	// Cette partie désactive l'état actif de pChildEDFail, et
	// faire de l'état mFailRID le nouvel état actif de pChildEDFail
	ExecutionData & pChildEDQuiescence = pChildECQuiescence->getwExecutionData();

	const AvmCode & scheduleCode =
			pChildEDQuiescence.getRuntimeFormOnSchedule(mQuiescenceRID.getPRID()).to< AvmCode >();

	pChildEDQuiescence.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);

	// Faire de l'état mQuiescenceRID le nouvel état actif de pChildEDQuiescence i.e. --> ED( Example.QUIESCENCE )
	pChildEDQuiescence.mwsetRuntimeFormOnScheduleAndIdle(mQuiescenceRID);
	/////////////////////////////////////////////////////////////

	if( mPortQuiencenceData.invalid() )
	{
		ExecutableForm * executablePortContainer = pChildEDQuiescence.getSystemRID().getExecutable();

		// create a new instance of Port with a port container
		PropertyPart & systempropertypart = const_cast< PropertyPart & >(
				executablePortContainer->getAstSystem().getPropertyPart() );

		Modifier modifier;
		modifier.setVisibilityPublic().setDirectionOutput();
		Port * astQuiescencePort = new Port(systempropertypart,
				"quiescence#data", IComPoint::IO_PORT_NATURE, modifier);
		systempropertypart.appendPort( BF(astQuiescencePort) );

		InstanceOfPort * aPortChildECQUIESCENCE =
				new InstanceOfPort(executablePortContainer, (* astQuiescencePort),
						executablePortContainer->getPort().size(), 0,
						IComPoint::IO_PORT_NATURE);

		aPortChildECQUIESCENCE->setRuntimeContainerRID(pChildEDQuiescence.getSystemRID());

		mPortQuiencenceData = executablePortContainer->savePort(aPortChildECQUIESCENCE);
	}

	const RuntimeID & portCompRID = getIORuntimeID( childEC->getIOElementTrace() );

	ExecutionConfiguration * quiescenceConfigTrace =
			new ExecutionConfiguration(portCompRID,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_OUTPUT_ENV,
							mPortQuiencenceData));

	BFList newFreshTrace;

	keepDelayOfTransition( childEC->getIOElementTrace(), newFreshTrace );

	pChildECQuiescence->getwExecutionData().setIOElementTrace(BF::REF_NULL);

	for (const auto & bfDelta : newFreshTrace )
	{
		ExecutionDataFactory::appendIOElementTrace(pChildEDQuiescence, bfDelta );
	}

	ExecutionDataFactory::appendIOElementTrace(pChildEDQuiescence,
			BF(quiescenceConfigTrace) );

	// ajout nécessaire pour pouvoir effectuer simplement la projection
	addRunnableTrace(pChildECQuiescence, portCompRID);

	// Create new instance of ExecutionCongtextFlags to replace old flags
	////////////////////////
	const ExecutionContextFlags * flags = new ExecutionContextFlags();

	pChildECQuiescence->setFlags( * flags );
	////////////////////////

	pChildECQuiescence->getwFlags().setObjectiveAbortedTrace();

	// get path condition from beginning to parent node anEC
	BF PCParentEC = parentEC->getExecutionData().getPathCondition();

	pChildEDQuiescence.setNodeCondition( guardDataQuiescenceTransition );

	pChildEDQuiescence.setPathCondition(
			ExpressionConstructor::andExpr(
					PCParentEC,
					pChildECQuiescence->getNodeCondition()));

	// add evaluation of guard of transition leading to pChildECQUIESCENCE to path condition of
	// node anEC (that is parent of pChildECQUIESCENCE)
	parentEC->appendChildContext(pChildECQuiescence);
}

void UnitaryTestCaseGeneratorProvider::addQuiescenceDuetoTimeInSpec(ExecutionContext * childEC,
		BF guardsTimeOutputTransitions, ExecutionContext * parentEC)
{
	BF guardDataQuiescenceTransition = ExpressionConstant::BOOLEAN_TRUE;
	BF guardTimeQuiescenceTransition;

	BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

	if ( guardsTimeOutputTransitions.isExpression() )
	{
		guardTimeQuiescenceTransition = ExpressionConstructor::forallExpr(
				delay,
				guardsTimeOutputTransitions.notExpr() );
	}
	else
	{
		if ( guardsTimeOutputTransitions == ExpressionConstant::BOOLEAN_FALSE )
		{
			guardTimeQuiescenceTransition = ExpressionConstant::BOOLEAN_TRUE;
		}
	}

	ExecutionContext * pChildECQuiescence = parentEC->cloneData(parentEC, true);

	pChildECQuiescence->getwExecutionData().setNodeCondition(
			guardDataQuiescenceTransition);

	//////////////////////////////////////////////////////////////
	// Cette partie désactive l'état actif de pChildEDFail, et
	// faire de l'état mFailRID le nouvel état actif de pChildEDFail
	ExecutionData & pChildEDQuiescence = pChildECQuiescence->getwExecutionData();

	const AvmCode & scheduleCode = pChildEDQuiescence.getRuntimeFormOnSchedule(mQuiescenceRID.getPRID()).to< AvmCode >();

	pChildEDQuiescence.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);

	// Faire de l'état mQuiescenceRID le nouvel état actif de pChildEDQuiescence i.e. --> ED( Example.QUIESCENCE )
	pChildEDQuiescence.mwsetRuntimeFormOnScheduleAndIdle(mQuiescenceRID);
	/////////////////////////////////////////////////////////////

	if( mPortQuiencenceTime.invalid() )
	{
		ExecutableForm * executablePortContainer = pChildEDQuiescence.getSystemRID().getExecutable();

		// create a new instance of Port with a port container
		PropertyPart & systempropertypart = const_cast< PropertyPart & >(
				executablePortContainer->getAstSystem().getPropertyPart() );

		Modifier modifier;
		modifier.setVisibilityPublic().setDirectionOutput();
		Port * astQuiescencePort = new Port(systempropertypart,
				"quiescence#time", IComPoint::IO_PORT_NATURE, modifier);
		systempropertypart.appendPort( BF(astQuiescencePort) );

		InstanceOfPort * aPortChildECQUIESCENCE =
				new InstanceOfPort(executablePortContainer, (* astQuiescencePort),
						executablePortContainer->getPort().size(), 0, IComPoint::IO_PORT_NATURE);

		aPortChildECQUIESCENCE->setRuntimeContainerRID(pChildEDQuiescence.getSystemRID());

		mPortQuiencenceTime = executablePortContainer->savePort(aPortChildECQUIESCENCE);
	}

	const RuntimeID & portCompRID = getIORuntimeID( childEC->getIOElementTrace() );

	ExecutionConfiguration * quiescenceConfigTrace =
			new ExecutionConfiguration(portCompRID,
					StatementConstructor::newCode(
							OperatorManager::OPERATOR_OUTPUT_ENV,
							mPortQuiencenceTime));

	BFList newFreshTrace;

	keepDelayOfTransition( childEC->getIOElementTrace(), newFreshTrace );

	BF ioTrace = pChildEDQuiescence.getIOElementTrace();

	pChildECQuiescence->getwExecutionData().setIOElementTrace(BF::REF_NULL);

	for (const auto & bfDelta : newFreshTrace )
	{
		ExecutionDataFactory::appendIOElementTrace(pChildEDQuiescence, bfDelta );
	}

	ExecutionDataFactory::appendIOElementTrace(pChildEDQuiescence,
			BF(quiescenceConfigTrace) );

	// ajout nécessaire pour pouvoir effectuer simplement la projection
	addRunnableTrace(pChildECQuiescence, portCompRID);

	// Create new instance of ExecutionCongtextFlags to replace old flags
	////////////////////////
	const ExecutionContextFlags * flags = new ExecutionContextFlags();

	pChildECQuiescence->setFlags( * flags );
	////////////////////////

	pChildECQuiescence->getwFlags().setObjectiveAbortedTrace();

	// get path condition from beginning to parent node anEC
	BF PtCParentEC = parentEC->getExecutionData().getPathTimedCondition();

	pChildEDQuiescence.setNodeTimedCondition( guardTimeQuiescenceTransition );

	pChildEDQuiescence.setPathTimedCondition(
			ExpressionConstructor::andExpr(
					PtCParentEC,
					pChildECQuiescence->getNodeTimedCondition()));

	// add evaluation of guard of transition leading to pChildECQUIESCENCE to path condition of
	// node anEC (that is parent of pChildECQUIESCENCE)
	parentEC->appendChildContext(pChildECQuiescence);
}

/**
 * postProcessing
 */

bool UnitaryTestCaseGeneratorProvider::postprocessImpl()
{
	AVM_OS_COUT << "PostProcess method for UnitaryTestCaseGeneratorProvider"<< std::endl;

	if ( mSequenceCoverage )
	{
		if ( mDeterministic )
		{
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << "************* YOUR MODEL IS DETERMINISTIC !**************" << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "------------- TEST CASE WILL BE GENERATED !--------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO

			// Here we have a list of symbolic execution graphs which includes a graph before projection
			// and the graphs which have been projected
			ListOfExecutionContext listGraphs = getConfiguration().getExecutionTrace();

			ExecutionContext::rw_child_iterator itListGraphs = listGraphs.begin();

			ExecutionContext * firstGraphBeforeProjection = * itListGraphs;

			OutStream out2File;

			int iteVectorOfPathConditions = 0;

			int itFilesTestCase = 1;

			addECToListECWithFlags( * firstGraphBeforeProjection );


			////////////////////////////////////////////////////////////////////////////
			// Get dataPathCondition and timePathCondition
			BF dataPathCondition;
			BF timePathCondition;

			ExecutionContext * lastChildEC = nullptr;

			ExecutionContext * nextEC = * itListGraphs;

			bool foundLastEC = false;

			while ( nextEC->hasChildContext() )
			{
				for ( const auto & aChild : nextEC->getChildContexts() )
				{
					if ( aChild->hasChildContext() )
					{
						nextEC = aChild;
					}

					if ( aChild->getwFlags().hasObjectiveAchievedTrace() )
					{
						lastChildEC = aChild;
						nextEC = aChild;
						foundLastEC = true;
					}
				}

				if ( foundLastEC ) break;
			}

			const sep::TableOfRuntimeT & tableOfRuntimes =
					lastChildEC->getExecutionData().getTableOfRuntime();

			for( const auto & runtime : tableOfRuntimes )
			{
				if ( runtime->getExecutable()->hasPort() &&
						runtime->getExecutable()->getSpecifier().hasFeatureLifeline() )
				{
					dataPathCondition = lastChildEC->getExecutionData().getPathCondition();
					timePathCondition = lastChildEC->getExecutionData().getPathTimedCondition();

					std::pair < std::string, BFList > newPair;
					newPair.first = runtime->getNameID();

					BFList listOfPathConditions;
					listOfPathConditions.append( dataPathCondition );
					listOfPathConditions.append( timePathCondition );
					newPair.second = listOfPathConditions;
					listOfPathConditions.clear();

					mVectorOfPathConditions.append(newPair);
				}
			}
			////////////////////////////////////////////////////////////////////////////

			itListGraphs++;

			mTestCaseGenerator.beginStream();

			// Create test case for localized components
			while ( itListGraphs != listGraphs.end() )
			{
				BFList listOfPathConditions = mVectorOfPathConditions.
						get(iteVectorOfPathConditions).second;

				BF pathDataCondition = listOfPathConditions.get(0);

				BF pathTimeCondition = listOfPathConditions.get(1);

				std::string nameMachine = mVectorOfPathConditions.
						get(iteVectorOfPathConditions).first;

				ExecutionContext * aProjectedGraph = * itListGraphs;

				addECToListECWithFlags( * aProjectedGraph );

				// specify Quiescence situations in projected graphs
				specifyQuiescence( * aProjectedGraph );

				// Take the projected graph completed by quiescence for test case generation
				generateTestCases( * aProjectedGraph,
						pathDataCondition,
						pathTimeCondition,
						nameMachine );

				// Write test case to a new file
				out2File = mTestCaseGenerator.getStream( "file#" + std::to_string(itFilesTestCase) );

				mTestcaseSystem->toStream( out2File );

				iteVectorOfPathConditions++;
				itFilesTestCase++;
				itListGraphs++;
			}

			mListECWithFlags.clear();
			///////////////////////////////////////////////////////////////////////

			mTestCaseGenerator.closeStream();

		}
		else
		{
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << "*********** YOUR MODEL IS NON-DETERMINISTIC !************" << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "----------------- NO TEST CASE GENERATED !---------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << "**** PLEASE ENSURE THAT YOUR MODEL IS DETERMINISTIC !****" << std::endl;//TODO
			AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO
		}
	}
	else if ( not mSequenceCoverage )
	{
		AVM_OS_COUT << std::endl;//TODO
		AVM_OS_COUT << std::endl;//TODO
		AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
		AVM_OS_COUT << "************ THE SEQUENCE IS NOT COVERED !**************" << std::endl;//TODO
		AVM_OS_COUT << "*********************************************************" << std::endl;//TODO
		AVM_OS_COUT << std::endl;//TODO
		AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
		AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
		AVM_OS_COUT << "----------------- NO TEST CASE GENERATED !---------------" << std::endl;//TODO
		AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
		AVM_OS_COUT << "---------------------------------------------------------" << std::endl;//TODO
		AVM_OS_COUT << std::endl;//TODO
		AVM_OS_COUT << std::endl;//TODO
	}

	return true;
}


void UnitaryTestCaseGeneratorProvider::deleteUnobservableDelays( ExecutionContext & anEC )
{
	BF newAtomicFormula;

	BF newPathTimeCondition =
			constructPtCwithoutInobservableDelays(
					newAtomicFormula, anEC.getPathTimedCondition() );

	anEC.getwExecutionData().setPathTimedCondition( newPathTimeCondition );

	for( const auto & itChildEC : anEC.getChildContexts() )
	{
		deleteUnobservableDelays( * itChildEC );
	}
}



void UnitaryTestCaseGeneratorProvider::specifyQuiescence( ExecutionContext & anEC )
{
	ListOfExecutionContext listChildECs = anEC.getChildContexts();

	ExecutionContext * nextChildEC = nullptr;

	InstanceOfPort * anInstancePort = nullptr;

	bool havingAllInputTransitions = true;

	BF guardsDataOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

	BF guardsTimedOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

	for ( const auto & childEC : listChildECs )
	{
		/*
		 * This part of code constructs the formula guardsOutputTransitions
		 * which are conjunction of all node conditions
		 * from a symbolic state. The objective of this code is to specify
		 *  the quiescence transitions.
		 */

		RuntimeID aRID;
		anInstancePort = getIOPort(childEC->getIOElementTrace(), aRID); // get port of childEC

		if (anInstancePort != nullptr)
		{
			if ( anInstancePort->getModifier().isDirectionOutput() )
			{
				guardsDataOutputTransitions =
						ExpressionConstructor::orExpr(guardsDataOutputTransitions,
							childEC->getNodeCondition());

				if ( mTimedModel )
				{
					guardsTimedOutputTransitions =
							ExpressionConstructor::orExpr(guardsTimedOutputTransitions,
								childEC->getNodeTimedCondition());
				}

				havingAllInputTransitions = false;
			}
		}

		if ( childEC->hasChildContext() || childEC->getFlags().hasCoverageElementTrace() )
		{
			nextChildEC = childEC;
		}
	}

	/*
	 * This part of code specifies quiescence transitions to symbolic execution
	 * in function of the guards of output transitions from a symbolic state
	 */
	if ( nextChildEC != nullptr )
	{
		if ( anEC.isnotRoot()  )
		{
			if ( havingAllInputTransitions )
			{
				guardsDataOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

				guardsTimedOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

				addQuiescenceDuetoDataInSpec(
						nextChildEC,
						guardsDataOutputTransitions,
						& anEC);

				if ( mTimedModel )
				{
					addQuiescenceDuetoTimeInSpec(
							nextChildEC,
							guardsTimedOutputTransitions,
							& anEC);
				}
			}
			else
			{
				if ( SolverFactory::isStrongSatisfiable(
						ExpressionConstructor::notExpr(guardsDataOutputTransitions)) )
				{
					addQuiescenceDuetoDataInSpec(
							nextChildEC,
							guardsDataOutputTransitions,
							& anEC);
				}

				if ( mTimedModel )
				{
					BF delay = getDelayOfTransition( nextChildEC->getIOElementTrace() );

					if ( SolverFactory::isStrongSatisfiable(
							ExpressionConstructor::forallExpr(delay,
							ExpressionConstructor::notExpr(guardsTimedOutputTransitions))) )
					{
						addQuiescenceDuetoTimeInSpec(
								nextChildEC,
								guardsTimedOutputTransitions,
								& anEC);
					}
				}
			}
		}
		specifyQuiescence( *nextChildEC );
	}
}


void UnitaryTestCaseGeneratorProvider::addECToListECWithFlags( const ExecutionContext & anEC )
{
	for( const auto & childEC : anEC.getChildContexts() )
	{
		mListECWithFlags.append(childEC);

		addECToListECWithFlags(* childEC);
	}
}


void UnitaryTestCaseGeneratorProvider::generateTestCases( ExecutionContext & rootProjectionEC,
		const BF & pathConditionTestPurpose,
		const BF & pathTimedConditionTestPurpose, std::string nameMachine )
{
	mTestcaseSystem = new System("TestCase");

	mStateMachine = Machine::newStatemachine(
			mTestcaseSystem, nameMachine,
			Specifier::DESIGN_PROTOTYPE_STATIC_SPECIFIER);

	mTestcaseSystem->saveOwnedElement(mStateMachine);

	if ( mTimedModel )
	{
		mTestcaseSystem->getwSpecifier().setFeatureTimed();
	}

	////////////////////////////////
	// Create the INCONC state and save it
	Machine * inconcState = Machine::newState(
			mStateMachine, mINCONCSTATE, Specifier::STATE_FINAL_MOC);
	mStateMachine->saveOwnedElement(inconcState);
	////////////////////////////////


	////////////////////////////////
	// Create the FAIL state and save it
	Machine * failState = Machine::newState(
			mStateMachine, mFAILSTATE, Specifier::STATE_FINAL_MOC);
	mStateMachine->saveOwnedElement(failState);
	////////////////////////////////


	////////////////////////////////
	// Create the PASS state and save it
	Machine * passState = Machine::newState(
			mStateMachine, mPASSSTATE, Specifier::STATE_FINAL_MOC);
	mStateMachine->saveOwnedElement(passState);
	////////////////////////////////

	////////////////////////////////
	// Create the interaction Part and save it
	mInteractionPart = mTestcaseSystem->getUniqInteraction();

	mConnector = &( mInteractionPart->appendConnector() );

	mConnector->setProtocol( ComProtocol::PROTOCOL_ENVIRONMENT_KIND );
	////////////////////////////////

	getAllExecutionContextsForResetClocks(pathTimedConditionTestPurpose);

	BF delayChildEC;

	for( const auto & childEC : mListECWithFlags )
	{
		if ( childEC->getFlags().hasObjectiveAchievedTrace()
				|| childEC->getFlags().hasCoverageElementTrace()
				|| childEC->getFlags().hasObjectiveAbortedTrace() )
		{
			delayChildEC = getDelayOfTransition( childEC->getIOElementTrace() );

			createNewTimeVariables(delayChildEC);

			for (const auto & delay : mListOfDelaysPtCTestPurpose)
			{
				if ( delayChildEC.isEQ(delay) )
				{
					mListECsToResetClock.append( childEC->getPrevious() );
				}
			}
		}
	}

	// Create clock in test case
	createClockForTestCase( delayChildEC );

	// Create bound B in test case
	createBoundBForTestCase();

	//New code to create test case from left graph
	createTransitionsInTestCase( rootProjectionEC, inconcState, failState,
			passState, pathConditionTestPurpose,
			pathTimedConditionTestPurpose,
			mClockTestCase );
}


void UnitaryTestCaseGeneratorProvider::createPassInTestCase(
		ExecutionContext * childEC,	Transition * tranPass,
		Machine * parentState, Machine * passState, Machine * failState,
		Machine * inconcState, const BF & clockTestCase, BFList OCond,
		BFList listInstDataVars, ListOfExecutionContext listECForInconc,
		BF pathConditionTestPurpose )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;
	InstanceOfPort * anInstanceOfPort =
			getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeResettingClock;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort,
			newFreshList, paramList);

	AvmCode::OperandCollectionT varsOfPort =
			getTermListOfPort( childEC->getIOElementTrace() );

	for ( const auto & varInst : varsOfPort)
	{
		listInstDataVars.append( varInst );
	}

	createNewVariables( newFreshList );

	BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

	// Add delay to the list of durations which have been instantiated
	listInstDataVars.append( delay );

	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		RoutingData aRoutingData =
				AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() ==
					ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				////////////////this code creates action//////////////////////
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				codeResettingClock = resettingClockTestCase(clockTestCase);

				// Get path condition pi(ec)
				BF guard = childEC->getPathCondition();

				// Get variables non instantiated in guardExpr
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated
				// if this variable becomes instantiated
				for ( auto varInst : listInstDataVars )
				{
					AvmCode::OperandCollectionT::iterator it =
							listOfVarsNonInstantiated.begin();

					while ( it != listOfVarsNonInstantiated.end() )
					{
						if ( *it == varInst )
						{
							it = listOfVarsNonInstantiated.erase( it );
						}
						else
						{
							++it;
						}
					}
				}
				////////////////////////////////////////////////////////////////

				// add OCond
				for ( const auto & cond : OCond)
				{
					guard = ExpressionConstructor::andExpr(
							guard, cond );
				}

				BFList paramsList =
						getParamsListOfPort(childEC->getIOElementTrace());

				BF oCondOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// add actual oCond
				guard = ExpressionConstructor::andExpr(
						guard, oCondOnFreshVars );


				// quantify existentially the guard
				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					guard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							guard );
				}
				else
				{
					guard = ExpressionConstructor::newExpr(
							guard );
				}


				// Creation of formulaPhiTilde which is negation of guard
				// constructed until now and will be used for
				// fail transition
				BF formulaPhiTilde =
						ExpressionConstructor::notExpr(guard);

				// add 'cl < B' to the guard
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_LT,
						clockTestCase, mBoundB ) );

				// add formula 'cl = z' to guardExpr
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ,
						clockTestCase, delay ) );

				BFCode guardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						guard );

				tranPass->setStatement(StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						action,
						guardBFCode,
						codeResettingClock ));

				tranPass->setTarget( *passState );

				parentState->saveOwnedElement( tranPass );


				// Create a new transition aTran whose source is parentState
				Transition * tranFail = new sep::Transition(* parentState );

				if (SolverFactory::isSatisfiable(formulaPhiTilde))
				{
					createFailForSpecifiedTransition( formulaPhiTilde,
							newFreshList, codeResettingClock, action, tranFail,
							parentState, failState, clockTestCase, delay,
							aRoutingData );
				}

			}
		}
	}

	// Associate EC with its corresponding state in test case in order to
	// determine parent of the state in test case
	std::pair<ExecutionContext *, Machine * > newPair;
	newPair.first = childEC;
	newPair.second = passState;
	mVectorOfECAndState.append(newPair);

	// Associate a state with its corresponding BSen
	mMapOfStateAndBSen[passState] = OCond;

	// Associate a state with its corresponding set of instantiated variables
	mMapOfStateAndDataVarsInst[passState] = listInstDataVars;
}


void UnitaryTestCaseGeneratorProvider::createQuiescenceInTestCase(
		ExecutionContext * childEC,	Transition * newTranInconc,
		Machine * parentState, Machine * inconcState,
		Machine * failState, const BF & clockTestCase,
		BFList OCond, BFList listInstVars )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newfreshList;
	BFList paramList;

	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeReadingClock;
	bool readValueOfClock = false;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newfreshList, paramList);

	// This code verifies whether we count duration by clock of test case
	for ( const auto & anEC : mListECsToResetClock )
	{
		if ( anEC == childEC->getPrevious() )
		{
			readValueOfClock = true;
			break;
		}
		else
		{
			readValueOfClock = false;
		}
	}
	///////////////////////////////////////////////////////////////////

	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		BFCode action = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT_ENV,
				INCR_BF(anInstanceOfPort), newfreshList );

		createNewVariables( newfreshList );

		if ( childEC->getNodeTimedCondition().isExpression() )
		{
			BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

			BF forallTimedGuard = childEC->getPathTimedCondition();

			if ( readValueOfClock )
			{
				codeReadingClock = readingValueOfClockTestCase( clockTestCase, delay );

				newTranInconc->setStatement( StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						forallTimedGuard, action, codeReadingClock ) );
			}
			else
			{
				newTranInconc->setStatement( StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						forallTimedGuard, action ) );
			}
		}
		else if ( childEC->getNodeCondition().isExpression() )
		{
			// add PC(st) in guardDataSecondTransition
			BF dataGuard = childEC->getPathCondition();

			// Get variables non instantiated in guardExpr
			AvmCode::OperandCollectionT listOfVarsNonInstantiated;

			getDataVarsNonInstantiatedInGuard(
					dataGuard,
					listOfVarsNonInstantiated );

			// This code erases a variable in listOfVarsNonInstantiated if this variable
			// becomes instantiated
			for ( const auto & varInst : listInstVars )
			{
				AvmCode::OperandCollectionT::iterator it = listOfVarsNonInstantiated.begin();
				while ( it != listOfVarsNonInstantiated.end() )
				{
					if ( *it == varInst )
					{
						it = listOfVarsNonInstantiated.erase( it );
					}
					else
					{
						++it;
					}
				}
			}
			//////////////////////////////////////////////////////////////////

			// add BSen in guardDataSecondTransition
			for (const auto & cond : OCond)
			{
				dataGuard = ExpressionConstructor::andExpr(
						dataGuard, cond );
			}

			if ( listOfVarsNonInstantiated.size() > 0 )
			{
				dataGuard = ExpressionConstructor::existsExpr(
						listOfVarsNonInstantiated,
						dataGuard );
			}

			BFCode existDataGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					dataGuard );


			// construction of time guard
			BF timedGuard = childEC->getPathTimedCondition();

			BFCode timedGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timedGuard );

			newTranInconc->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					existDataGuardBFCode, timedGuardBFCode, action ) ) ;
		}

		newTranInconc->setTarget( *inconcState );

		parentState->saveOwnedElement( newTranInconc );
	}
}

void UnitaryTestCaseGeneratorProvider::createInconcInTestCase(
		ExecutionContext * childEC,	Transition * aTran,
		Machine * parentState, Machine * failState,
		Machine * inconcState, const BF & clockTestCase,
		BFList OCond, BFList listInstDataVars,
		ListOfExecutionContext listECForInconc, BF pathConditionTestPurpose )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;

	InstanceOfPort * anInstanceOfPort =
			getIOPort(childEC->getIOElementTrace(), portCompRID);

	BFCode codeResettingClock;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort,
			newFreshList, paramList);

	createNewVariables( newFreshList );

	AvmCode::OperandCollectionT varsOfPort =
			getTermListOfPort( childEC->getIOElementTrace() );

	createNewVariables( varsOfPort );

	BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

	// Add delay to the list listInstDataVars which have been instantiated
	listInstDataVars.append( delay );

	if ( anInstanceOfPort->getwModifier().isDirectionOutput() )
	{
		RoutingData aRoutingData =
				AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if ( aRoutingData.valid() )
		{
			if ( aRoutingData.getProtocol() ==
					ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				////////////////this code creates action//////////////////////
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				codeResettingClock = resettingClockTestCase(clockTestCase);


				// Get path condition pi(ec)
				BF guard = childEC->getPathCondition();

				// Get variables non instantiated in guardDataSecondTransition
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( auto varInst : listInstDataVars )
				{
					AvmCode::OperandCollectionT::iterator it =
							listOfVarsNonInstantiated.begin();

					while ( it != listOfVarsNonInstantiated.end() )
					{
						if ( *it == varInst )
						{
							it = listOfVarsNonInstantiated.erase( it );
						}
						else
						{
							++it;
						}
					}
				}
				////////////////////////////////////////////////////////////////

				// add OCond
				for ( const auto & cond : OCond)
				{
					guard = ExpressionConstructor::andExpr(
							guard, cond );
				}

				BFList paramsList =
						getParamsListOfPort(childEC->getIOElementTrace());

				BF oCondOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// add actual oCond
				guard = ExpressionConstructor::andExpr(
						guard, oCondOnFreshVars );


				// quantify existentially the guard
				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					guard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							guard );
				}
				else
				{
					guard = ExpressionConstructor::newExpr(
							guard );
				}


				// Creation of formulaPhiTilde which is negation of guard
				// constructed until now and will be used for
				// fail transition
				BF formulaPhiTilde =
						ExpressionConstructor::notExpr(guard);

				// add 'cl < B' to the guard
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_LT,
						clockTestCase, mBoundB ) );

				// add formula 'cl = z' to guardExpr
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ,
						clockTestCase, delay ) );

				BFCode guardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						guard );



				aTran->setStatement(StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						action,
						guardBFCode,
						codeResettingClock ));

				aTran->setTarget( *inconcState );

				parentState->saveOwnedElement(aTran);


				// Create a new transition aTran whose source is parentState
				Transition * tranFail = new sep::Transition(* parentState );

				if (SolverFactory::isSatisfiable(formulaPhiTilde))
				{
					createFailForSpecifiedTransition( formulaPhiTilde,
							newFreshList, codeResettingClock, action, tranFail,
							parentState, failState, clockTestCase, delay,
							aRoutingData );
				}














//				InstanceOfPort * childECPort =
//						getIOPort( childEC->getIOElementTrace() );
//
//				BF pathConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;
//
//				BF pathTimeConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;
//
//				for ( const auto & anEC : listECForInconc )
//				{
//					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
//					{
//						if ( SolverFactory::isStrongSatisfiable(
//								ExpressionConstructor::andExpr(
//										childEC->getNodeCondition(),
//										anEC->getNodeCondition() ) ) )
//						{
//							/*
//							 * this code create inconc state due to data
//							 */
//							///////////////////////////////////////////////////////
//							createInconcOutputForSamePortInTestCase( anEC,
//									itmState, inconcState, failState, OCond,
//									listInstDataVars, newFreshList,
//									pathConditionInconcs,
//									pathTimeConditionInconcs );
//							////////////////end of Code create inconc////////////////
//						}
//
//						mListOfTreatedECs.append( anEC );
//					}
//				}
//
//				// this code create fail state due to data
//				///////////////////////////////////////////////////////
//				createFailDueToSpecifiedTransition( childEC, itmState,
//						failState, OCond, listInstDataVars, newFreshList,
//						pathConditionInconcs, pathTimeConditionInconcs );
//				////////////////end of Code create Fail////////////////

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
			{

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
			{

			}
		}
	}
	else if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		for ( const auto & varInst : varsOfPort)
		{
			listInstDataVars.append( varInst );
		}

		if (anInstanceOfPort->getwModifier().isVisibilityPublic())
		{
			RoutingData aRoutingData =
					AvmCommunicationFactory::searchInputRoutingData(
							childEC->getExecutionData(),
							*anInstanceOfPort, portCompRID);

			if (aRoutingData.valid())
			{
				if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					BFCode action = StatementConstructor::newCode(
							OperatorManager::OPERATOR_OUTPUT,
							INCR_BF(anInstanceOfPort), newFreshList );

					aTran->setStatement( action );

					aTran->setTarget( *inconcState );

					parentState->saveOwnedElement( aTran );

					InstanceOfPort * childECPort =
							getIOPort( childEC->getIOElementTrace() );

					for ( const auto & anEC : listECForInconc )
					{
						if ( childECPort ==
								getIOPort( anEC->getIOElementTrace() ) )
						{
							mListOfTreatedECs.append( anEC );
						}
					}
				}
				else if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_BUFFER_KIND )
				{

				}
				else if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_MULTICAST_KIND )
				{

				}
			}
		}
		else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
		{
			RoutingData aRoutingData =
					AvmCommunicationFactory::searchInputRoutingData(
							childEC->getExecutionData(),
							*anInstanceOfPort, portCompRID);

			if (aRoutingData.valid())
			{
				if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					/*
					 * Create guard
					 */
					// add pathConditionTestPurpose to guardExpr
					BF guard = ExpressionConstructor::newExpr(
							childEC->getPathCondition() );

					// Get variables non instantiated in guardExpr
					AvmCode::OperandCollectionT listOfDataVarsNonInstantiated;
					getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
							listOfDataVarsNonInstantiated );

					// This code erases a variable in listOfVarsNonInstantiated
					// if this variable becomes instantiated
					for ( const auto & varInst : listInstDataVars )
					{
						AvmCode::OperandCollectionT::iterator it =
								listOfDataVarsNonInstantiated.begin();
						while ( it != listOfDataVarsNonInstantiated.end() )
						{
							if ( *it == varInst )
							{
								it = listOfDataVarsNonInstantiated.erase( it );
							}
							else
							{
								++it;
							}
						}
					}
					////////////////////////////////////////////////////////////

					// add formula 'cl = z' to guardExpr
					guard = ExpressionConstructor::andExpr(
							guard, ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_EQ,
							clockTestCase, delay ) );

					// add cond to guard
					for ( const auto & cond : OCond)
					{
						guard = ExpressionConstructor::andExpr( guard, cond );
					}

					// quantify existentially the guard
					if ( listOfDataVarsNonInstantiated.size() > 0 )
					{
						guard = ExpressionConstructor::existsExpr(
								listOfDataVarsNonInstantiated,
								guard );
					}
					else
					{
						guard = ExpressionConstructor::newExpr( guard );
					}

					// add 'cl < B' to the guard
					guard = ExpressionConstructor::andExpr(
							guard, ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_LT,
							clockTestCase, mBoundB ) );


					BFCode guardBFCode = StatementConstructor::newCode(
							OperatorManager::OPERATOR_GUARD,
							guard );

					/*
					 * Create action
					 */
					BFCode action = StatementConstructor::newCode(
							OperatorManager::OPERATOR_INPUT,
							INCR_BF(anInstanceOfPort), varsOfPort );

					codeResettingClock = resettingClockTestCase(clockTestCase);

					aTran->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action,
							guardBFCode,
							codeResettingClock ));

					aTran->setTarget( *inconcState );

					parentState->saveOwnedElement( aTran );

					InstanceOfPort * childECPort =
							getIOPort( childEC->getIOElementTrace() );

					for ( const auto & anEC : listECForInconc )
					{
						if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
						{
							mListOfTreatedECs.append( anEC );
						}
					}
				}
				else if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_BUFFER_KIND )
				{

				}
				else if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_MULTICAST_KIND )
				{

				}
			}
		}
	}
}


void UnitaryTestCaseGeneratorProvider::createInconcUnderSpecifiedInTestCase(
		BF formulaPhiTilde, AvmCode::OperandCollectionT varsOfPort,
		BFCode codeResettingClock, BFCode action, Transition * aTran,
		Machine * parentState, Machine * inconcState, const BF & clockTestCase,
		RoutingData aRoutingData )
{
	BFList paramList;

	createNewVariables( varsOfPort );

	if (aRoutingData.valid())
	{
		if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
		{
			/*
			 * Create guard
			 */
			// add pathConditionTestPurpose to guardExpr
			BF guard = ExpressionConstructor::newExpr(
					formulaPhiTilde );

			// add 'cl < B' to the guard
			guard = ExpressionConstructor::andExpr(
					guard, ExpressionConstructor::newExpr(
					OperatorManager::OPERATOR_LT,
					clockTestCase, mBoundB ) );

			BFCode guardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					guard );

			aTran->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					action,
					guardBFCode,
					codeResettingClock ));

			aTran->setTarget( *inconcState );

			parentState->saveOwnedElement( aTran );
		}
		else if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_BUFFER_KIND )
		{

		}
		else if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_MULTICAST_KIND )
		{

		}
	}
}


void UnitaryTestCaseGeneratorProvider::createFailForTimeInTestCase(
		ExecutionContext * childEC,	Machine * newState,
		Transition * newTran, Machine * parentState, Machine * failState,
		const BF & clockTestCase, BFList OCond, BFList listInstVars )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT varsOfPort = getTermListOfPort( childEC->getIOElementTrace() );
	AvmCode::OperandCollectionT newfreshList;
	BFList paramList;
	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeReadingClock;
	bool readValueOfClock = false;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newfreshList, paramList);

	createNewVariables(varsOfPort);

	for ( const auto & varInst : varsOfPort)
	{
		listInstVars.append( varInst );
	}

	// This code verifies whether we count duration by clock of test case
	for ( const auto & anEC : mListECsToResetClock )
	{
		if ( anEC == childEC->getPrevious() )
		{
			readValueOfClock = true;
			break;
		}
		else
		{
			readValueOfClock = false;
		}
	}
	///////////////////////////////////////////////////////////////////


	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		BFCode action = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT,
				INCR_BF(anInstanceOfPort), varsOfPort );

		BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

		if ( readValueOfClock )
		{
			codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

			newTran->setStatement(StatementConstructor::newCodeFlat(
					OperatorManager::OPERATOR_SEQUENCE,
					action, codeReadingClock ));
		}
		else
		{
			newTran->setStatement( action );
		}

		if ( childEC->getNodeTimedCondition().isExpression() )
		{
			mStateMachine->saveOwnedElement(newState);
			mIndexState++;

			newTran->setTarget( *newState );

			parentState->saveOwnedElement( newTran );

			Transition * newTranFail = new sep::Transition( *newState );

			BF timedGuard = ExpressionConstructor::newExpr(
					childEC->getNodeTimedCondition() );

			BFCode timedGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timedGuard );

			newTranFail->setStatement( timedGuardBFCode );

			newTranFail->setTarget( *failState );

			newState->saveOwnedElement( newTranFail );
		}
		else
		{
			newTran->setTarget( *failState );

			parentState->saveOwnedElement( newTran );
		}
	}
}



void UnitaryTestCaseGeneratorProvider::createInconcOutputForSamePortInTestCase(
		ExecutionContext * childEC, Machine * itmState, Machine * inconcState,
		Machine * failState, BFList OCond, BFList listInstDataVars,
		AvmCode::OperandCollectionT newFreshList, BF & pathConditionInconcs,
		BF & pathTimeConditionInconcs )
{
	// Create equality expression on fresh vars
	///////////////////////////////////////////////
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFList paramList;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newFreshList, paramList);

	BFList paramsList = getParamsListOfPort(childEC->getIOElementTrace());

	BF equalityOnFreshVars = createEqualityOnFreshVars(
			childEC, newFreshList, listInstDataVars, paramsList );
	///////////////////////////////////////////////

	AvmCode::OperandCollectionT varsOfPort = getTermListOfPort( childEC->getIOElementTrace() );
	for ( const auto & varInst : varsOfPort)
	{
		listInstDataVars.append( varInst );
	}

	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		// add PC of parent of childEC to guardExpr
		BF dataGuard = ExpressionConstructor::newExpr(
				childEC->getPathCondition() );

		// Get variables non instantiated in guardExpr
		AvmCode::OperandCollectionT listOfVarsNonInstantiated;
		getDataVarsNonInstantiatedInGuard( dataGuard,
				listOfVarsNonInstantiated );

		// This code erases a variable in listOfVarsNonInstantiated if this variable
		// becomes instantiated
		for ( const auto & varInst : listInstDataVars)
		{
			AvmCode::OperandCollectionT::iterator it = listOfVarsNonInstantiated.begin();
			while ( it != listOfVarsNonInstantiated.end() )
			{
				if ( *it == varInst )
				{
					it = listOfVarsNonInstantiated.erase( it );
				}
				else
				{
					++it;
				}
			}
		}
		//////////////////////////////////////////////////////////////////

		// conjunct BSen to guardExpr
		for ( const auto & cond : OCond )
		{
			dataGuard = ExpressionConstructor::andExpr(
					dataGuard, cond );
		}

		dataGuard = ExpressionConstructor::andExpr(
				dataGuard,
				equalityOnFreshVars );

		BF existsDataGuard = ExpressionConstant::BOOLEAN_TRUE;

		if ( listOfVarsNonInstantiated.empty() )
		{
			existsDataGuard = ExpressionConstructor::newExpr(
					dataGuard );
		}
		else
		{
			existsDataGuard = ExpressionConstructor::existsExpr(
					listOfVarsNonInstantiated, dataGuard );
		}

		if ( SolverFactory::isStrongSatisfiable( existsDataGuard ) )
		{
			BFCode action = StatementConstructor::newCode(
					OperatorManager::OPERATOR_INPUT,
					INCR_BF(anInstanceOfPort), varsOfPort );

			BFCode existsGuardCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					existsDataGuard );

			Transition * newTranInconc = new sep::Transition( *itmState );

			newTranInconc->setStatement( existsGuardCode ) ;

			newTranInconc->setTarget( *inconcState );

			itmState->saveOwnedElement( newTranInconc );

			pathConditionInconcs = ExpressionConstructor::orExpr(
					pathConditionInconcs,
					dataGuard );

			if ( childEC->getPathTimedCondition().isExpression() )
			{
				BF timedGuard = ExpressionConstructor::newExpr(
						childEC->getPathTimedCondition() );

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );

				newTranInconc->setStatement( StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						existsGuardCode, timedGuardBFCode) );

				pathTimeConditionInconcs = ExpressionConstructor::orExpr(
						pathTimeConditionInconcs,
						timedGuard );
			}
		}
	}
}


void UnitaryTestCaseGeneratorProvider::createFailForSpecifiedTransition(
		BF formulaPhiTilde, AvmCode::OperandCollectionT varsOfPort,
		BFCode codeResettingClock, BFCode action, Transition * tranFail,
		Machine * parentState, Machine * failState, const BF & clockTestCase,
		BF delay, RoutingData aRoutingData )
{
	BFList paramList;

	createNewVariables( varsOfPort );

	if (aRoutingData.valid())
	{
		if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
		{
			/*
			 * Create guard
			 */
			// add pathConditionTestPurpose to guardExpr
			BF guard = ExpressionConstructor::newExpr(
					formulaPhiTilde );

			// add 'cl < B' to the guard
			guard = ExpressionConstructor::andExpr(
					guard, ExpressionConstructor::newExpr(
					OperatorManager::OPERATOR_LT,
					clockTestCase, mBoundB ) );

			// add formula 'cl = z' to guardExpr
			guard = ExpressionConstructor::andExpr(
					guard, ExpressionConstructor::newExpr(
					OperatorManager::OPERATOR_EQ,
					clockTestCase, delay ) );

			BFCode guardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					guard );

			tranFail->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					action,
					guardBFCode,
					codeResettingClock ));

			tranFail->setTarget( *failState );

			parentState->saveOwnedElement( tranFail );
		}
		else if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_BUFFER_KIND )
		{

		}
		else if ( aRoutingData.getProtocol() ==
				ComProtocol::PROTOCOL_MULTICAST_KIND )
		{

		}
	}
}


void UnitaryTestCaseGeneratorProvider::createFailRemainingPortsInTestCase(
		InstanceOfPort * aRemainingPort, ExecutionContext * nextEC,
		Transition * newTranFail, Machine * parentState, Machine * failState,
		const BF & clockTestCase, BFList listInstDataVars )
{
	const RuntimeID & portCompRID = aRemainingPort->getRuntimeContainerRID();
	AvmCode::OperandCollectionT varsOfPort;
	BFList paramList;

	ENV.createNewFreshParam(portCompRID, *aRemainingPort,
			varsOfPort, paramList);

	createNewVariables(varsOfPort);

	BF codeResettingClock = resettingClockTestCase(clockTestCase);

	for ( const auto & varInst : varsOfPort)
	{
		listInstDataVars.append( varInst );
	}

	BF delay = getDelayOfTransition( nextEC->getIOElementTrace() );

	listInstDataVars.append( delay );

	if ( aRemainingPort->getwModifier().isDirectionOutput() )
	{
		// Creation of first transition having port
		BFCode action = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT,
				INCR_BF( aRemainingPort ), varsOfPort );

		// add pathTimedConditionTestPurpose to guardExpr
		BF guard = ExpressionConstructor::newExpr(
				ExpressionConstant::BOOLEAN_TRUE );

		// add 'cl < B' to the guard
		guard = ExpressionConstructor::andExpr(
				guard, ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_LT,
				clockTestCase, mBoundB ) );

		// add formula 'cl = z' to guardExpr
		guard = ExpressionConstructor::andExpr(
				guard, ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_EQ,
				clockTestCase, delay ) );

		BFCode guardBFCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				guard );

		newTranFail->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				action,
				guardBFCode,
				codeResettingClock ) ) ;

		newTranFail->setTarget( *failState );

		parentState->saveOwnedElement( newTranFail );
	}
}

void UnitaryTestCaseGeneratorProvider::createInconcRemainingInputPortsInTestCase(
		InstanceOfPort * aRemainingPort, ExecutionContext * nextEC,
		Transition * newTranInconc, Machine * parentState, Machine * inconcState,
		const BF & clockTestCase, BFList listInstDataVars )
{
	const RuntimeID & portCompRID = aRemainingPort->getRuntimeContainerRID();
	AvmCode::OperandCollectionT varsOfPort;
	BFList paramList;

	ENV.createNewFreshParam(portCompRID, *aRemainingPort,
			varsOfPort, paramList);

	createNewVariables(varsOfPort);

	BF codeResettingClock = resettingClockTestCase(clockTestCase);

	for ( const auto & varInst : varsOfPort)
	{
		listInstDataVars.append( varInst );
	}

	BF delay = getDelayOfTransition( nextEC->getIOElementTrace() );

	listInstDataVars.append( delay );

	if ( aRemainingPort->getwModifier().isDirectionInput() )
	{
		// Creation of first transition having port
		BFCode action = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT,
				INCR_BF( aRemainingPort ), varsOfPort );

		// add pathTimedConditionTestPurpose to guardExpr
		BF guard = ExpressionConstructor::newExpr(
				ExpressionConstant::BOOLEAN_TRUE );

		// add 'cl < B' to the guard
		guard = ExpressionConstructor::andExpr(
				guard, ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_LT,
				clockTestCase, mBoundB ) );

		// add formula 'cl = z' to guardExpr
		guard = ExpressionConstructor::andExpr(
				guard, ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_EQ,
				clockTestCase, delay ) );

		BFCode guardBFCode = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				guard );

		newTranInconc->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				action,
				guardBFCode,
				codeResettingClock ) ) ;

		newTranInconc->setTarget( *inconcState );

		parentState->saveOwnedElement( newTranInconc );
	}
}


void UnitaryTestCaseGeneratorProvider::createCoveredInTestCase(
		ExecutionContext * childEC,	Machine * newState, Transition * aTran,
		Machine * parentState, Machine * failState, Machine * inconcState,
		BF pathConditionTestPurpose, const BF & clockTestCase, BFList OCond,
		BFList listInstDataVars, ListOfExecutionContext listECForInconc )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;
	InstanceOfPort * anInstanceOfPort =
			getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeResettingClock;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort,
			newFreshList, paramList);

	AvmCode::OperandCollectionT varsOfPort =
			getTermListOfPort( childEC->getIOElementTrace() );

	BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

	// Add delay to the list listInstDataVars which have been instantiated
	listInstDataVars.append( delay );

	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		RoutingData aRoutingData =
				AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() ==
					ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				createNewVariables(newFreshList);

				////////////////this code creates action//////////////////////
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				codeResettingClock = resettingClockTestCase(clockTestCase);


				// Get path condition pi(ec)
				BF guard = childEC->getPathCondition();

				// Get variables non instantiated in guardDataSecondTransition
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated
				// if this variable becomes instantiated
				for ( auto varInst : listInstDataVars )
				{
					AvmCode::OperandCollectionT::iterator it =
							listOfVarsNonInstantiated.begin();

					while ( it != listOfVarsNonInstantiated.end() )
					{
						if ( *it == varInst )
						{
							it = listOfVarsNonInstantiated.erase( it );
						}
						else
						{
							++it;
						}
					}
				}
				////////////////////////////////////////////////////////////////

				// add OCond
				for ( const auto & cond : OCond)
				{
					guard = ExpressionConstructor::andExpr(
							guard, cond );
				}

				BFList paramsList =
						getParamsListOfPort(childEC->getIOElementTrace());

				BF oCondOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// add actual oCond
				guard = ExpressionConstructor::andExpr(
						guard, oCondOnFreshVars );


				// quantify existentially the guard
				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					guard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							guard );
				}
				else
				{
					guard = ExpressionConstructor::newExpr(
							guard );
				}


				// Creation of formulaPhiTilde which is negation of guard
				// constructed until now and will be used for
				// fail transition
				BF formulaPhiTilde =
						ExpressionConstructor::notExpr(guard);

				// add 'cl < B' to the guard
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_LT,
						clockTestCase, mBoundB ) );

				// add formula 'cl = z' to guardExpr
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ,
						clockTestCase, delay ) );

				BFCode guardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						guard );

				aTran->setStatement(StatementConstructor::newCode(
						OperatorManager::OPERATOR_SEQUENCE,
						action,
						guardBFCode,
						codeResettingClock ));

				mStateMachine->saveOwnedElement(newState);
				mIndexState++;

				aTran->setTarget( *newState );

				parentState->saveOwnedElement( aTran );


				// Create a new transition aTran whose source is parentState
				Transition * tranFail = new sep::Transition(* parentState );

				if (SolverFactory::isSatisfiable(formulaPhiTilde))
				{
					createFailForSpecifiedTransition( formulaPhiTilde,
							newFreshList, codeResettingClock, action, tranFail,
							parentState, failState, clockTestCase, delay,
							aRoutingData );
				}

				// add oCondOnFreshVars to OCond
				OCond.append(oCondOnFreshVars);
			}
		}
	}
	else if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		for ( const auto & varInst : varsOfPort)
		{
			listInstDataVars.append( varInst );
		}

		if (anInstanceOfPort->getwModifier().isVisibilityPublic())
		{
			RoutingData aRoutingData =
					AvmCommunicationFactory::searchInputRoutingData(
							childEC->getExecutionData(), *anInstanceOfPort,
							portCompRID);

			if (aRoutingData.valid())
			{
				if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					createNewVariables( varsOfPort );

					/*
					 * Create guard
					 */
					// add pathConditionTestPurpose to guard
					BF guard = ExpressionConstructor::newExpr(
							pathConditionTestPurpose );

					// Get variables non instantiated in guardExpr
					AvmCode::OperandCollectionT listOfDataVarsNonInstantiated;
					getDataVarsNonInstantiatedInGuard( guard,
							listOfDataVarsNonInstantiated );

					// This code erases a variable in listOfVarsNonInstantiated if
					// this variable becomes instantiated
					for ( const auto & varInst : listInstDataVars )
					{
						AvmCode::OperandCollectionT::iterator it =
								listOfDataVarsNonInstantiated.begin();
						while ( it != listOfDataVarsNonInstantiated.end() )
						{
							if ( *it == varInst )
							{
								it = listOfDataVarsNonInstantiated.erase( it );
							}
							else
							{
								++it;
							}
						}
					}
					////////////////////////////////////////////////////////////////

					// add OCond to guard
					for ( const auto & cond : OCond)
					{
						guard = ExpressionConstructor::andExpr( guard, cond );
					}

					// quantify existentially the guard
					if ( listOfDataVarsNonInstantiated.size() > 0 )
					{
						guard = ExpressionConstructor::existsExpr(
								listOfDataVarsNonInstantiated,
								guard );
					}
					else
					{
						guard = ExpressionConstructor::newExpr( guard );
					}

					// add formula 'cl = z' to guardExpr
					guard = ExpressionConstructor::andExpr(
							guard, ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_EQ,
							clockTestCase, delay ) );

					BFCode guardBFCode = StatementConstructor::newCode(
							OperatorManager::OPERATOR_GUARD,
							guard );

					/*
					 * Create action
					 */
					BFCode action = StatementConstructor::newCode(
							OperatorManager::OPERATOR_OUTPUT,
							INCR_BF(anInstanceOfPort), varsOfPort );

					codeResettingClock = resettingClockTestCase(clockTestCase);

					aTran->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							guardBFCode,
							action,
							codeResettingClock ));

					mStateMachine->saveOwnedElement(newState);
					mIndexState++;

					aTran->setTarget( *newState );

					parentState->saveOwnedElement( aTran );


					InstanceOfPort * childECPort =
							getIOPort( childEC->getIOElementTrace() );

					for ( const auto & anEC : listECForInconc )
					{
						if ( childECPort ==
								getIOPort( anEC->getIOElementTrace() ) )
						{
							mListOfTreatedECs.append( anEC );
						}
					}
				}
			}
		}
		else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
		{
			RoutingData aRoutingData =
					AvmCommunicationFactory::searchInputRoutingData(
							childEC->getExecutionData(), *anInstanceOfPort,
							portCompRID);

			if (aRoutingData.valid())
			{
				if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					// Add varsOfPort of internal input to listInstDataVars
					for ( const auto & varInst : varsOfPort)
					{
						listInstDataVars.append( varInst );
					}

					createNewVariables( varsOfPort );

					/*
					 * Create guard
					 */
					// add pi(ec) to guard
					BF guard = ExpressionConstructor::newExpr(
							childEC->getPathCondition() );

					// Get variables non instantiated in guardExpr
					AvmCode::OperandCollectionT listOfDataVarsNonInstantiated;
					getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
							listOfDataVarsNonInstantiated );

					// This code erases a variable in listOfVarsNonInstantiated
					// if this variable becomes instantiated
					for ( const auto & varInst : listInstDataVars )
					{
						AvmCode::OperandCollectionT::iterator it =
								listOfDataVarsNonInstantiated.begin();
						while ( it != listOfDataVarsNonInstantiated.end() )
						{
							if ( *it == varInst )
							{
								it = listOfDataVarsNonInstantiated.erase( it );
							}
							else
							{
								++it;
							}
						}
					}
					////////////////////////////////////////////////////////////

					// add cond to guard
					for ( const auto & cond : OCond)
					{
						guard = ExpressionConstructor::andExpr( guard, cond );
					}

					if ( guard != ExpressionConstant::BOOLEAN_TRUE )
					{
						// quantify existentially the guard
						if ( listOfDataVarsNonInstantiated.size() > 0 )
						{
							guard = ExpressionConstructor::existsExpr(
									listOfDataVarsNonInstantiated,
									guard );
						}
						else
						{
							guard = ExpressionConstructor::newExpr( guard );
						}
					}
					else
					{
						guard = ExpressionConstant::BOOLEAN_TRUE;
					}


					// Creation of formulaPhiTilde which is negation of guard
					// constructed until now and will be used for
					// under-specified internal input
					BF formulaPhiTilde =
							ExpressionConstructor::notExpr(guard);

					// add 'cl < B' to the guard
					guard = ExpressionConstructor::andExpr(
							guard, ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_LT,
							clockTestCase, mBoundB ) );

					// add formula 'cl = z' to guardExpr
					guard = ExpressionConstructor::andExpr(
							guard, ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_EQ,
							clockTestCase, delay ) );


					BFCode guardBFCode = StatementConstructor::newCode(
							OperatorManager::OPERATOR_GUARD,
							guard );

					/*
					 * Create action
					 */
					BFCode action = StatementConstructor::newCode(
							OperatorManager::OPERATOR_INPUT,
							INCR_BF(anInstanceOfPort), varsOfPort );

					codeResettingClock = resettingClockTestCase(clockTestCase);

					aTran->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action,
							guardBFCode,
							codeResettingClock ));

					mStateMachine->saveOwnedElement(newState);
					mIndexState++;

					aTran->setTarget( *newState );

					parentState->saveOwnedElement( aTran );


					InstanceOfPort * childECPort =
							getIOPort( childEC->getIOElementTrace() );

					for ( const auto & anEC : listECForInconc )
					{
						if ( childECPort ==
								getIOPort( anEC->getIOElementTrace() ) )
						{
							mListOfTreatedECs.append( anEC );
						}
					}

					// Create a new transition aTran whose source is parentState
					Transition * aTran = new sep::Transition(* parentState );

					if (SolverFactory::isSatisfiable(formulaPhiTilde))
					{
						createInconcUnderSpecifiedInTestCase( formulaPhiTilde,
								varsOfPort, codeResettingClock, action, aTran,
								parentState, inconcState, clockTestCase,
								aRoutingData );
					}
				}
			}
		}
	}

	// Associate EC with its corresponding state in test case in order to
	// determine parent of the state in test case
	std::pair<ExecutionContext *, Machine * > newPair;
	newPair.first = childEC;
	newPair.second = newState;
	mVectorOfECAndState.append(newPair);

	// Associate a state with its corresponding BSen
	mMapOfStateAndBSen[newState] = OCond;

	// Associate a state with its corresponding set of instantiated variables
	mMapOfStateAndDataVarsInst[newState] = listInstDataVars;
}


void UnitaryTestCaseGeneratorProvider::createTransitionsInTestCase(
		ExecutionContext & anEC, Machine * inconcState, Machine * failState,
		Machine * passState, const BF & pathConditionTestPurpose,
		const BF & pathTimedConditionTestPurpose, const BF & clockTestCase )
{
	Transition * initialTransition = nullptr;
	Machine * newState = nullptr;
	ExecutionContext * nextEC = nullptr;

	Vector<InstanceOfPort *> tableOfOutputPorts;

	Vector<InstanceOfPort *> tableOfInputPorts;

	bool isInstantiatedListOfOutputPorts = false;

	bool isInstantiatedListOfInputPorts = false;

	Transition * newTran = nullptr;
	Machine * parentState = nullptr;
	BFList OCond;
	BFList listInstDataVars;

	// the case of first EC
	if ( !anEC.hasPrevious() )
	{
		////////////////////////////////
		// Create the initial state and save it
		Machine * initialState = Machine::newState(
				mStateMachine, mINITIALSTATE, Specifier::STATE_START_MOC);
		mStateMachine->saveOwnedElement(initialState);
		////////////////////////////////

		////////////////////////////////
		// Create the initial transition and save it
		initialTransition = new sep::Transition(* initialState );
		initialTransition->setNameID("startup");
		initialState->saveOwnedElement( initialTransition );
		////////////////////////////////

		// Associate an EC with its corresponding state in test case in order to
		// determine parent of the state in test case
		std::pair<ExecutionContext *, Machine * > newPairECState;
		newPairECState.first = &anEC;
		newPairECState.second = initialState;
		mVectorOfECAndState.append(newPairECState);

		// Associate a state with its corresponding OCond
		BFList OCond;
		OCond.append(ExpressionConstant::BOOLEAN_TRUE);
		mMapOfStateAndBSen[newState] = OCond;

		// Associate a state with its set of instantiated vars
		BFList listInstDataVars;
		mMapOfStateAndDataVarsInst[newState] = listInstDataVars;
	}

	// This code rearrange all ECs in child ECs of anEC
	// in order to put EC having childEC in the first position
	ListOfExecutionContext originalListChildECs = anEC.getChildContexts();

	ListOfExecutionContext orderedListChildECs;

	ExecutionContext::rw_child_iterator it = originalListChildECs.begin();

	while ( it != originalListChildECs.end() )
	{
		if ( (*it)->getFlags().hasCoverageElementTrace() ||
				(*it)->getFlags().hasObjectiveAchievedTrace()	)
		{
			orderedListChildECs.append( *it );

			it = originalListChildECs.erase( it );
		}
		else
		{
			++it;
		}
	}

	for ( const auto & childEC : originalListChildECs )
	{
		orderedListChildECs.append( childEC );
	}
	/////////////////////////////////////////////////////////////


	for ( const auto & childEC : orderedListChildECs )
	{
		/////////////////// This code creates new Port ///////////////////
		// newPort = true requires to create a new Port, and not otherwise
		bool newPort = true;

		Port * aPort = nullptr;

		RuntimeID & portCompRID = RuntimeID::REF_NULL;

		AvmCode::OperandCollectionT newFreshList;

		InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);

		if ( anInstanceOfPort != nullptr )
		{
			BFList paramList;
			ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newFreshList, paramList);

			if ( mVectorOfPortAndRID.size() == 0 )
			{
				// Create a port and save it in xLIA test case
				aPort = createNewPort( childEC, newFreshList, anInstanceOfPort, portCompRID );

				createNewComRoute( childEC, anInstanceOfPort, aPort, portCompRID );
			}

			for (const auto & pair : mVectorOfPortAndRID)
			{
				if (pair.second != anInstanceOfPort)
				{
					newPort = true;
				}
				else
				{
					newPort = false;
					break;
				}
			}

			if ( newPort )
			{
				aPort = createNewPort( childEC, newFreshList, anInstanceOfPort, portCompRID );

				createNewComRoute( childEC, anInstanceOfPort, aPort, portCompRID );
			}
		}
		///////////////////////////////////////////////////////////////////////

//		////////////////////////////////
//		// Create a new state and save it
//		newState = Machine::newState(
//				mStateMachine, "q_" + std::to_string( anEC.getIdNumber() ),
//				Specifier::STATE_SIMPLE_MOC );
//		////////////////////////////////

		////////////////////////////////
		// Create a new state and save it
		newState = Machine::newState(
				mStateMachine, "q_" + std::to_string( mIndexState ),
				Specifier::STATE_SIMPLE_MOC );
		////////////////////////////////


		/////////////////// This code creates new types Enum ///////////////////

		// Create a new type enum and save it in xLIA test case
		createNewTypesEnum(newFreshList);
		///////////////////////////////////////////////////////////////////////

		for (const auto & pair : mVectorOfECAndState)
		{
			if ( childEC->getPrevious() == pair.first )
			{
				parentState = pair.second;

				newTran = new sep::Transition(* parentState );

				OCond = mMapOfStateAndBSen[pair.second];
				listInstDataVars = mMapOfStateAndDataVarsInst[pair.second];
			}
		}

		BF nodeCondition = childEC->getwExecutionData().getNodeCondition();

		BFCode guard = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				nodeCondition );

		// Create new data variables in test case
		AvmCode::OperandCollectionT listOfVarsNonInstantiated;
		getDataVarsNonInstantiatedInGuard( pathConditionTestPurpose,
				listOfVarsNonInstantiated );
		////////////////////////////////

		if ( childEC->getFlags().hasObjectiveAchievedTrace() )
		{
			ListOfExecutionContext listECForInconc = childEC->getPrevious()->getChildContexts();

			// This code erases childEC in listECForInconc
			ExecutionContext::rw_child_iterator it = listECForInconc.begin();

			while ( it != listECForInconc.end() )
			{
				if ( *it == childEC )
				{
					it = listECForInconc.erase( it );
				}
				else
				{
					++it;
				}
			}
			//////////////////////////////////////////////////////////////////

			createPassInTestCase( childEC, newTran, parentState,
					passState, failState, inconcState, clockTestCase,
					OCond, listInstDataVars, listECForInconc,
					pathConditionTestPurpose );
		}
		else if ( childEC->getFlags().hasObjectiveInconclusiveTrace() )
		{
			bool treatThisEC = false;

			for ( const auto & treatedEC : mListOfTreatedECs )
			{
				if ( childEC == treatedEC )
				{
					treatThisEC = true;
					break;
				}
				else
				{
					treatThisEC = false;
				}
			}

			if ( not treatThisEC )
			{
				ListOfExecutionContext listECForInconc = childEC->getPrevious()->getChildContexts();

				// This code erases childEC in listECForInconc
				ExecutionContext::rw_child_iterator it = listECForInconc.begin();

				while ( it != listECForInconc.end() )
				{
					if ( *it == childEC )
					{
						it = listECForInconc.erase( it );
					}
					else
					{
						++it;
					}
				}
				//////////////////////////////////////////////////////////////////

				createInconcInTestCase( childEC, newTran, parentState,
						failState, inconcState, clockTestCase,
						OCond, listInstDataVars,
						listECForInconc, pathConditionTestPurpose );
			}
		}
		else if ( childEC->getFlags().hasCoverageElementTrace() )
		{
			ListOfExecutionContext listECForInconc = childEC->getPrevious()->getChildContexts();

			// This code erases childEC in listECForInconc
			ExecutionContext::rw_child_iterator it = listECForInconc.begin();

			while ( it != listECForInconc.end() )
			{
				if ( *it == childEC )
				{
					it = listECForInconc.erase( it );
				}
				else
				{
					++it;
				}
			}
			//////////////////////////////////////////////////////////////////

			createCoveredInTestCase( childEC, newState,
					newTran, parentState, failState, inconcState,
					pathConditionTestPurpose, clockTestCase,
					OCond, listInstDataVars,
					listECForInconc );
		}
		else if ( childEC->getFlags().hasObjectiveAbortedTrace() )
		{
			if ( childEC->getNodeCondition().isExpression() ||
					childEC->getNodeTimedCondition().isExpression() )
			{
				createQuiescenceInTestCase( childEC, newTran,
						parentState, inconcState, failState,
						clockTestCase, OCond, listInstDataVars );
			}
		}
		else if ( childEC->getFlags().hasObjectiveTimeoutTrace() )
		{
			createFailForTimeInTestCase(childEC, newState, newTran, parentState,
					failState, clockTestCase, OCond, listInstDataVars );
		}
		else
		{
			mStateMachine->saveOwnedElement(newState);
			mIndexState++;

			initialTransition->setTarget( *newState );

			//	 Associate EC with its corresponding state in test case in order to
			// determine parent of the state in test case
			std::pair<ExecutionContext *, Machine * > newPair;
			newPair.first = childEC;
			newPair.second = newState;
			mVectorOfECAndState.append(newPair);

			// Associate a state with its corresponding OCond
			BFList OCond;
			OCond.append(ExpressionConstant::BOOLEAN_TRUE);
			mMapOfStateAndBSen[newState] = OCond;

			// Associate a state with its corresponding BSen
			BFList instDataVars;
			mMapOfStateAndDataVarsInst[newState] = instDataVars;
		}

		if ( anInstanceOfPort != nullptr )
		{
			// Get list of output ports in model
			if ( not isInstantiatedListOfOutputPorts )
			{
				getListOfOutputPorts( anInstanceOfPort, tableOfOutputPorts );

				isInstantiatedListOfOutputPorts = true;
			}

			verifyTreatedOutputPortForFail(tableOfOutputPorts, anInstanceOfPort);


			// Get list of input ports in model
			if ( not isInstantiatedListOfInputPorts )
			{
				getListOfInputPorts( anInstanceOfPort, tableOfInputPorts );

				isInstantiatedListOfInputPorts = true;
			}

			verifyTreatedInputPortForInconc(tableOfInputPorts, anInstanceOfPort);
		}

		// Determine nextEC
		if ( childEC->hasChildContext()
			|| childEC->getwFlags().hasObjectiveAchievedTrace() )
		{
			nextEC = childEC;
		}
	}

	if ( nextEC != nullptr )
	{
		if ( not tableOfOutputPorts.empty() )
		{
			for( const auto & aRemainingPort : tableOfOutputPorts )
			{
				bool newPort = true;

				Port * aPort = nullptr;

				ArrayOfBF & listOfParams = aRemainingPort->getParameters();

				for (const auto & pair : mVectorOfPortAndRID)
				{
					if (pair.second != aRemainingPort)
					{
						newPort = true;
					}
					else
					{
						newPort = false;
						break;
					}
				}

				if ( newPort )
				{
					aPort = createNewPortForRemainingInstanceOfPort(
							listOfParams, aRemainingPort );

					createNewComRouteForRemainingInstanceOfPort(
							aRemainingPort, aPort );
				}

				for (const auto & pair : mVectorOfECAndState)
				{
					if ( nextEC->getPrevious() == pair.first )
					{
						parentState = pair.second;
						newTran = new sep::Transition( * parentState );
						OCond = mMapOfStateAndBSen[pair.second];
						listInstDataVars = mMapOfStateAndDataVarsInst[pair.second];
					}
				}

				if ( nextEC->getPrevious()->isnotRoot() )
				{
					createFailRemainingPortsInTestCase( aRemainingPort,
						nextEC, newTran, parentState, failState,
						clockTestCase, listInstDataVars );
				}
			}
		}

		if ( not tableOfInputPorts.empty() )
		{
			for( const auto & aRemainingPort : tableOfInputPorts )
			{
				if (aRemainingPort->getwModifier().isVisibilityPrivate())
				{
					bool newPort = true;

					Port * aPort = nullptr;

					ArrayOfBF & listOfParams = aRemainingPort->getParameters();

					for (const auto & pair : mVectorOfPortAndRID)
					{
						if (pair.second != aRemainingPort)
						{
							newPort = true;
						}
						else
						{
							newPort = false;
							break;
						}
					}

					if ( newPort )
					{
						aPort = createNewPortForRemainingInstanceOfPort(
								listOfParams, aRemainingPort );

						createNewComRouteForRemainingInstanceOfPort(
								aRemainingPort, aPort );
					}

					for (const auto & pair : mVectorOfECAndState)
					{
						if ( nextEC->getPrevious() == pair.first )
						{
							parentState = pair.second;
							newTran = new sep::Transition( * parentState );
							OCond = mMapOfStateAndBSen[pair.second];
							listInstDataVars = mMapOfStateAndDataVarsInst[pair.second];
						}
					}

					if ( nextEC->getPrevious()->isnotRoot() )
					{
						createInconcRemainingInputPortsInTestCase( aRemainingPort,
							nextEC, newTran, parentState, inconcState,
							clockTestCase, listInstDataVars );
					}
				}
			}
		}

		createTransitionsInTestCase( *nextEC, inconcState, failState,
				passState, pathConditionTestPurpose,
				pathTimedConditionTestPurpose, clockTestCase );
	}
}

Port * UnitaryTestCaseGeneratorProvider::createNewPort( ExecutionContext * anEC,
		AvmCode::OperandCollectionT newfreshList,
		InstanceOfPort * anInstanceOfPort,
		RuntimeID & portCompRID )
{
	// Create a port and save it in xLIA test case
	//////////////////////////////////////////////
	Modifier & modifier = Modifier::PROPERTY_UNDEFINED_MODIFIER;

	modifier.setVisibilityPublic();

	if ( anInstanceOfPort != nullptr )
	{
		if ( anInstanceOfPort->getModifier().isDirectionInput() )
		{
			RoutingData aRoutingData =
					AvmCommunicationFactory::searchInputRoutingData(
							anEC->getExecutionData(), *anInstanceOfPort, portCompRID);

			if (aRoutingData.valid())
			{
				if ( aRoutingData.getProtocol() ==
						ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					if (anInstanceOfPort->getwModifier().isVisibilityPublic())
					{
						modifier.setDirectionOutput();
					}
					else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
					{
						modifier.setDirectionInput();
					}
				}
			}
		}
		else if ( anInstanceOfPort->getModifier().isDirectionOutput() )
		{
			modifier.setDirectionInput();
		}
	}

	Port * aPort = new sep::Port(mStateMachine->getPropertyPart(),
			anInstanceOfPort->str(), IComPoint::IO_PORT_NATURE,
			modifier);

	for ( const auto & var : newfreshList )
	{
		const InstanceOfData & varInstance = var.to< InstanceOfData >();

		const BaseTypeSpecifier & typeSpecifier = varInstance.getTypeSpecifier();

		BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

		Variable * param = new sep::Variable( mStateMachine,
				sep::Modifier::PROPERTY_PARAMETER_MODIFIER,
				typeVar, "",
				 BF::REF_NULL );

		aPort->saveParameter( param );
	}

	// Associate RID with its corresponding Port
	std::pair<Port *, InstanceOfPort * > newPair;
	newPair.first = aPort;
	newPair.second = anInstanceOfPort;
	mVectorOfPortAndRID.append(newPair);

	mStateMachine->saveOwnedElement( aPort );

	return aPort;
}

Port * UnitaryTestCaseGeneratorProvider::createNewPortForRemainingInstanceOfPort(
		ArrayOfBF & listOfParams,
		InstanceOfPort * anInstanceOfPort )
{
	// Create a port and save it in xLIA test case
	//////////////////////////////////////////////
	Modifier & modifier = Modifier::PROPERTY_UNDEFINED_MODIFIER;

	modifier.setVisibilityPublic();

	if ( anInstanceOfPort != nullptr )
	{
		if ( anInstanceOfPort->getModifier().isDirectionInput() )
		{
			if (anInstanceOfPort->getwModifier().isVisibilityPublic())
			{
				modifier.setDirectionOutput();
			}
			else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
			{
				modifier.setDirectionInput();
			}
		}
		else if ( anInstanceOfPort->getModifier().isDirectionOutput() )
		{
			modifier.setDirectionInput();
		}
	}

	Port * aPort = new sep::Port(mStateMachine->getPropertyPart(),
			anInstanceOfPort->str(), IComPoint::IO_PORT_NATURE,
			modifier);

	for ( const auto & var : listOfParams )
	{
		const InstanceOfData & varInstance = var.to< InstanceOfData >();

		const BaseTypeSpecifier & typeSpecifier = varInstance.getTypeSpecifier();

		BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

		Variable * param = new sep::Variable( mStateMachine,
				sep::Modifier::PROPERTY_PARAMETER_MODIFIER,
				typeVar, "",
				 BF::REF_NULL );

		aPort->saveParameter( param );
	}

	// Associate RID with its corresponding Port
	std::pair<Port *, InstanceOfPort * > newPair;
	newPair.first = aPort;
	newPair.second = anInstanceOfPort;
	mVectorOfPortAndRID.append(newPair);

	mStateMachine->saveOwnedElement( aPort );

	return aPort;
}

void UnitaryTestCaseGeneratorProvider::createNewComRoute(
		ExecutionContext * anEC, InstanceOfPort * anInstanceOfPort,
		Port * aPort,
		RuntimeID & portCompRID )
{
	sep::ComPoint comPoint;

	sep::ComRoute * comRoute = new sep::ComRoute( mConnector );

	if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		RoutingData aRoutingData = AvmCommunicationFactory::searchInputRoutingData(
				anEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() ==
					ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				if (anInstanceOfPort->getwModifier().isVisibilityPublic())
				{
					comRoute = &(mConnector->appendComRoute(
							sep::Modifier::PROPERTY_OUTPUT_DIRECTION ));
				}
				else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
				{
					comRoute = &(mConnector->appendComRoute(
							sep::Modifier::PROPERTY_INPUT_DIRECTION ));
				}
			}
		}

		comPoint = comRoute->appendComPoint(mStateMachine, aPort);
	}
	else if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		sep::ComRoute & comRoute = mConnector->appendComRoute(
				sep::Modifier::PROPERTY_INPUT_DIRECTION );

		comRoute.appendComPoint(mStateMachine, aPort);
	}
}

void UnitaryTestCaseGeneratorProvider::createNewComRouteForRemainingInstanceOfPort(
		InstanceOfPort * anInstanceOfPort,
		Port * aPort )
{
	sep::ComPoint comPoint;

	if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		if (anInstanceOfPort->getwModifier().isVisibilityPublic())
		{
			sep::ComRoute & comRoute = mConnector->appendComRoute(
					sep::Modifier::PROPERTY_OUTPUT_DIRECTION );

			comPoint = comRoute.appendComPoint(mStateMachine, aPort);
		}
		else if (anInstanceOfPort->getwModifier().isVisibilityPrivate())
		{
			sep::ComRoute & comRoute = mConnector->appendComRoute(
					sep::Modifier::PROPERTY_INPUT_DIRECTION );

			comPoint = comRoute.appendComPoint(mStateMachine, aPort);
		}
	}
	else if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		sep::ComRoute & comRoute = mConnector->appendComRoute(
				sep::Modifier::PROPERTY_INPUT_DIRECTION );

		comRoute.appendComPoint(mStateMachine, aPort);
	}
}

BF UnitaryTestCaseGeneratorProvider::createNewTypesEnum(AvmCode::OperandCollectionT newFreshList)
{
//	DataType * enumT;
	PropertyPart & declPropertyPart = mTestcaseSystem->getPropertyPart();
	BF typeEnum;

	bool newEnum = true;

	for ( const auto & var : newFreshList )
	{
		InstanceOfData * varInstance = var.to_ptr< InstanceOfData >();

		const BaseTypeSpecifier & typeSpecifier = varInstance->getTypeSpecifier();

		if (typeSpecifier.isTypedEnum())
		{
			typeEnum = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

			for (const auto & anEnum : mListOfEnum)
			{
				if ( typeEnum == anEnum )
				{
					newEnum = false;
					break;
				}
				else
				{
					newEnum = true;
				}
			}

			if ( newEnum )
			{
				if( typeSpecifier.hasAstElement() )
				{
				       declPropertyPart.appendDataType(
				    		   INCR_BF( const_cast< DataType * >
				               	   (& typeSpecifier.getAstDataType()) ));
				}
				else
				{

				       declPropertyPart.appendDataType( typeEnum );

				}
				mListOfEnum.append( typeEnum );
			}
		}
	}

	return typeEnum;
}


void UnitaryTestCaseGeneratorProvider::createBoundBForTestCase()
{
	const std::string BOUND_B = "B";

//	TypeSpecifier typeBoundB( TypeManager::POS_RATIONAL );
//
//	Variable * boundB = new sep::Variable( mStateMachine,
//			sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
//			typeBoundB, BOUND_B,
//			BF::REF_NULL );
//
//	mStateMachine->saveOwnedElement( boundB );
//
//	mListVariablesTestCase.append( boundB );

	mBoundB = mStateMachine->saveOwnedElement(
			new sep::Variable( mStateMachine,
				sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
				TypeManager::POS_RATIONAL, BOUND_B, BF::REF_NULL ) );
}


void UnitaryTestCaseGeneratorProvider::createClockForTestCase( BF delay )
{
//	bool isDenseTimed = getConfiguration().getSpecification().getSpecifier().hasFeatureDenseTimed();
//
//	TypeSpecifier timeType( TypeManager::newClockTime(TYPE_CLOCK_SPECIFIER,
//			isDenseTimed ? TypeManager::URATIONAL : TypeManager::UINTEGER) );

	mClockTestCase = mStateMachine->saveOwnedElement(
			new sep::Variable( mStateMachine,
					sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
					TypeManager::URATIONAL, "cl_TC", BF::REF_NULL ) );

}

void UnitaryTestCaseGeneratorProvider::createNewTimeVariables(BF delay)
{
	if ( delay.is<InstanceOfData>() )
	{
		bool newTimedVar = true;

		bool isDenseTimed = getConfiguration().getSpecification().
				getSpecifier().hasFeatureDenseTimed();

		TypeSpecifier timeType( TypeManager::newClockTime(TYPE_TIME_SPECIFIER,
				isDenseTimed ? TypeManager::URATIONAL : TypeManager::UINTEGER) );

		Variable * newVariable = new sep::Variable( mStateMachine,
				sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
				timeType, delay.str(),
				BF::REF_NULL );

		if ( mListVariablesTestCase.size() > 0 )
		{
			for ( const auto & variableInList : mListVariablesTestCase)
			{
				if ( variableInList->getFullyQualifiedNameID() !=
						newVariable->getFullyQualifiedNameID() )
				{
					newTimedVar = true;
				}
				else
				{
					newTimedVar = false;
					break;
				}
			}
		}
		else
		{
			mStateMachine->saveOwnedElement( newVariable );

			mListVariablesTestCase.append( newVariable );

			newTimedVar = false;
		}

		if ( newTimedVar )
		{
			mStateMachine->saveOwnedElement( newVariable );

			mListVariablesTestCase.append( newVariable );
		}
	}
}


void UnitaryTestCaseGeneratorProvider::createNewVariables(AvmCode::OperandCollectionT termsListOfPort)
{
	for ( const auto & var : termsListOfPort )
	{
		if ( not var.isNumber() )
		{
			bool createNewVar = true;

			InstanceOfData * varInstance = var.to_ptr< InstanceOfData >();

			const BaseTypeSpecifier & typeSpecifier =
					varInstance->getTypeSpecifier();

			BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

			Variable * newVariable = new sep::Variable( mStateMachine,
					sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
					typeVar, var.str(),
					BF::REF_NULL );

			if ( mListVariablesTestCase.size() > 0 )
			{
				for ( const auto & variableInList : mListVariablesTestCase)
				{
					if ( variableInList->getFullyQualifiedNameID() !=
							newVariable->getFullyQualifiedNameID() )
					{
						createNewVar = true;
					}
					else
					{
						createNewVar = false;
						break;
					}
				}
			}
			else
			{
				mStateMachine->saveOwnedElement( newVariable );

				mListVariablesTestCase.append( newVariable );

				createNewVar = false;
			}

			if ( createNewVar )
			{
				mStateMachine->saveOwnedElement( newVariable );

				mListVariablesTestCase.append( newVariable );
			}
		}
	}
}


///////////////////////////////////////////////////////////////////////////
// Some useful methods
//
//	getConfiguration().getSpecification(); // xlia parse model AST
//
//	getConfiguration().getExecutableSystem(); // the model after execution phase
//
//	getConfiguration().getExecutionTrace(); // Execution graph, obtained by symbolic execution (Symbolic Tree)
//
//	getExecutionQueue(); // The queue contains the next symbolic states which are not evaluated yet
//
//	getControllerUnitManager(); // Allows the access to all instanciated FAM
//
//	// getControllerUnitManager().getMainProcessor(); // module supervisor
//
//	getConfiguration().getWorkflow(); // Workflow contains user's configurations of symbolic execution
//
//	getSymbexRequestManager().postRequestStop(this); // request stop: stop symbolic execution
//
// end of useful methods
///////////////////////////////////////////////////////////////////////////

}
