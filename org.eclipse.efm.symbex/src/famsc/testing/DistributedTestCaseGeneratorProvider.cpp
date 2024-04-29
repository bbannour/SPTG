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

#include "DistributedTestCaseGeneratorProvider.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionDataFactory.h>
#include <computer/primitive/AvmCommunicationFactory.h>

#include <famsc/testing/TestCaseGenerator.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/symbol/Symbol.h>
#include <fml/expression/ExpressionTypeChecker.h>
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

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/Workflow.h>

#include <solver/api/SolverFactory.h>

namespace sep
{

/**
 * CONSTRUCTOR
 */
DistributedTestCaseGeneratorProvider::DistributedTestCaseGeneratorProvider(TestCaseGenerator & aTestCaseGenerator)
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
mMapOfStateAndTimeVarsInst ( ),
mVectorOfPortAndRID ( ),
mListOfConnector ( ),
mListOfEnum ( ),
mListVariablesTestCase ( ),
mListECWithFlags ( ),
mIndexState ( ),
mConnector ( ),
mInteractionPart ( ),
mListOfDelaysPtCTestPurpose ( ),
mListECsToResetClock ( ),
mTStart ( ),
mClockTestCase ( ),
mListOfTreatedECs ( ),
mINITIALSTATE ("initialstate"),
mPASSSTATE ("PASS"),
mINCONCSTATE ("INCONC"),
mFAILSTATE ("FAIL"),
mVectorOfPathConditions( )
{

}

bool DistributedTestCaseGeneratorProvider::postprocessImpl()
{
	AVM_OS_COUT << "PostProcess method for DistributedTestCaseGeneratorProvider"<< std::endl;

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

			AVM_OS_COUT << "lastChildEC : " << lastChildEC->str() << std::endl;//TODO

			const sep::TableOfRuntimeT & tableOfRuntimes =
					lastChildEC->getExecutionData().getTableOfRuntime();

			for( const auto & runtime : tableOfRuntimes )
			{
				if ( runtime->getExecutable()->hasPort() &&
						runtime->getExecutable()->getSpecifier().hasFeatureLifeline() )
				{
					dataPathCondition = runtime->getDataByNameID("localPC");
					timePathCondition = runtime->getDataByNameID("localPtC");

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
				const BFList & listOfPathConditions = mVectorOfPathConditions.get(iteVectorOfPathConditions).second;

				AVM_OS_DEBUG << std::endl;
				AVM_OS_DEBUG << "(*itListGraphs)->str() : " << (*itListGraphs)->str() << std::endl
						<< " with nameMachine : " << mVectorOfPathConditions.get(iteVectorOfPathConditions).first << std::endl
						<< " HAS dataPathCondition : " << listOfPathConditions.get(0).str() << std::endl
						<< " and timePathCondition : " << listOfPathConditions.get(1).str() << std::endl;//TODO
				AVM_OS_DEBUG << std::endl;

				ExecutionContext * aProjectedGraph = * itListGraphs;

				addECToListECWithFlags( * aProjectedGraph );

				// specify Quiescence situations in projected graphs
//				specifyQuiescence( * aProjectedGraph );

				// Take the projected graph completed by quiescence for test case generation
				generateTestCases( * aProjectedGraph,
						listOfPathConditions.get(0),
						listOfPathConditions.get(1),
						mVectorOfPathConditions.get(iteVectorOfPathConditions).first );

				// Write test case to a new file
				out2File = mTestCaseGenerator.getStream( "file#" + std::to_string(itFilesTestCase) );

				mTestcaseSystem->toStream( out2File );

				itFilesTestCase++;

				iteVectorOfPathConditions++;
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

bool DistributedTestCaseGeneratorProvider::configureImpl(const WObject * wfParameterObject)
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

		AVM_OS_COUT << "The parameters are correctly defined for DistributedTestCaseGeneratorProvider..." << std::endl;

	}
	else {

		AVM_OS_COUT << "The parameters are not correctly defined for DistributedTestCaseGeneratorProvider !" << std::endl;

	}

	aConfigFlag = true;

	return aConfigFlag;
}

/**
 * preFiltering
 */
bool DistributedTestCaseGeneratorProvider::prefilter(ExecutionContext & anEC)
{
//	AVM_OS_COUT << "prefilter test DistributedTestCaseGeneratorProvider"<< std::endl;

	return true;
}


void DistributedTestCaseGeneratorProvider::getAllExecutionContextsForResetClocks(
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


//void DistributedTestCaseGeneratorProvider::createFailDueToTimeInGraph(
//		ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd)
//{
//	for ( const auto & anEC : mListOfECWithOutputPort )
//	{
//		ExecutionContext * childEC = anEC;
//
//		RuntimeID & portCompRID = RuntimeID::REF_NULL;
//		AvmCode::OperandCollectionT newFreshList;
//		InstanceOfPort * aPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
//		BFList paramList;
//
//		ENV.createNewFreshParam(portCompRID, *aPort, newFreshList, paramList);
//
//		ExecutionContext * pChildECFail = nullptr;
//
//		pChildECFail = childEC->cloneData(parentEC, true); // clone childEC to a new execution context for verdict Fail
//
//		//////////////////////////////////////////////////////////////
//		// Cette partie désactive l'état actif de pChildEDFail, et
//		// faire de l'état mFailRID le nouvel état actif de pChildEDFail
//		// donc on peut changer l'étiquette de l'état symbolique FAIL
//		ExecutionData & pChildEDFail = pChildECFail->getwExecutionData();
//
//		// Désactiver l'état actif de pChildEDFail i.e. --> ED( Example.s4 )
//		const AvmCode & scheduleCode = pChildEDFail.getRuntimeFormOnSchedule(mFailRID.getPRID()).to< AvmCode >();
//		pChildEDFail.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);
//
//		// Faire de l'état mFailRID le nouvel état actif de pChildEDFail i.e. --> ED( Example.QUIESCENCE )
//		pChildEDFail.mwsetRuntimeFormOnScheduleAndIdle(mFailRID);
//		//////////////////////////////////////////////////////////////
//
//
//		// Create new instance of ExecutionCongtextFlags to replace old flags
//		////////////////////////
//		const ExecutionContextFlags * flags = new ExecutionContextFlags();
//
//		pChildECFail->setFlags( * flags );
//		////////////////////////
//
//		pChildECFail->getwFlags().setObjectiveTimeoutTrace();
//
//		ExecutionConfiguration * failDueTimeConfigTrace =
//				new ExecutionConfiguration(portCompRID,
//					StatementConstructor::newCode(
//						OperatorManager::OPERATOR_OUTPUT_ENV,
//						INCR_BF(aPort), newFreshList));
//
//		BFList newFreshTrace;
//
//		// keep the delays from iotrace in newFreshTrace and take off other infos
//		keepDelayOfTransition( childEC->getIOElementTrace(), newFreshTrace );
//
//		pChildECFail->getwExecutionData().setIOElementTrace(BF::REF_NULL);
//
//		for (const auto & bfDelta : newFreshTrace )
//		{
//			ExecutionDataFactory::appendIOElementTrace(pChildECFail->getwExecutionData(), bfDelta );
//		}
//
//		ExecutionDataFactory::appendIOElementTrace(pChildECFail->getwExecutionData(),
//				BF(failDueTimeConfigTrace) );
//
//		// ajout nécessaire pour pouvoir effectuer simplement la projection
//		addRunnableTrace(pChildECFail, portCompRID);
//
//		pChildECFail->getwExecutionData().appendParameters( paramList );
//
//		BF nodeCondition = ExpressionConstructor::newExpr(childEC->getNodeCondition());
//
//		// get path condition from beginning to parent node anEC
//		BF PCParentEC = parentEC->getExecutionData().getPathCondition();
//
//		BF equalityOnFreshVars = createEqualityOnFreshVarsForGraph(
//				childEC, newFreshList );
//
//		pChildECFail->getwExecutionData().setNodeCondition(
//				ExpressionConstructor::andExpr(
//						nodeCondition,
//						equalityOnFreshVars));
//
//		pChildECFail->getwExecutionData().setPathCondition(
//				ExpressionConstructor::andExpr(
//						PCParentEC,
//						pChildECFail->getNodeCondition()));
//
//		//////////////////////////////////////////////////////////////
//		// Cette partie construit le Path Timed Condition du FAIL
//		// (dans le cas d'un automate temporisé)
//		if ( childEC->getwExecutionData().getNodeTimedCondition().isExpression() )
//		{
//			BF nodeTimedConditionFail = ExpressionConstructor::notExpr(
//					childEC->getNodeTimedCondition());
//
//			// get path condition from beginning to parent node anEC
//			BF PTCParentEC = parentEC->getExecutionData().getPathTimedCondition();
//
//			pChildECFail->getwExecutionData().setNodeTimedCondition(nodeTimedConditionFail);
//
//			BF pathTimedCondition = ExpressionConstructor::andExpr(
//					PTCParentEC,
//					pChildECFail->getNodeTimedCondition());
//
//			pChildECFail->getwExecutionData().setPathTimedCondition(pathTimedCondition);
//
//			listofECToAdd.append( pChildECFail );
//		}
//		//////////////////////////////////////////////////////////////
//	}
//}
//
//
//void DistributedTestCaseGeneratorProvider::createFailDueToDataInGraph(
//		ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd)
//{
//	for (const auto & anEC : mListOfECWithOutputPort)
//	{
//		ExecutionContext * childEC = anEC;
//
//		BFList paramsList = getParamsListOfPort(anEC->getIOElementTrace());
//
//		RuntimeID & portCompRID = RuntimeID::REF_NULL;
//		AvmCode::OperandCollectionT newFreshList;
//		InstanceOfPort * aPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
//		BFList paramList;
//
//		ENV.createNewFreshParam(portCompRID, *aPort, newFreshList, paramList);
//
//		BF notEqualityOnFreshVars = createNotEqualityOnFreshVars(
//				childEC, portCompRID, newFreshList, aPort );
//
//		ExecutionContext * pChildECFail = nullptr;
//
//		pChildECFail = childEC->cloneData(parentEC, true);
//
//		//////////////////////////////////////////////////////////////
//		// Cette partie désactive l'état actif de pChildEDFail, et
//		// faire de l'état mFailRID le nouvel état actif de pChildEDFail
//		// donc on peut changer l'étiquette de l'état symbolique FAIL
//		ExecutionData & pChildEDFail = pChildECFail->getwExecutionData();
//
//		// Désactiver l'état actif de pChildEDFail i.e. --> ED( Example.s4 )
//		const AvmCode & scheduleCode = pChildEDFail.getRuntimeFormOnSchedule(mFailRID.getPRID()).to< AvmCode >();
//		pChildEDFail.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);
//
//		// Faire de l'état mFailRID le nouvel état actif de pChildEDFail i.e. --> ED( Example.QUIESCENCE )
//		pChildEDFail.mwsetRuntimeFormOnScheduleAndIdle(mFailRID);
//		//////////////////////////////////////////////////////////////
//
//
//		// Create new instance of ExecutionCongtextFlags to replace old flags
//		////////////////////////
//		const ExecutionContextFlags * flags = new ExecutionContextFlags();
//
//		pChildECFail->setFlags( * flags );
//		////////////////////////
//
//		pChildECFail->getwFlags().setObjectiveFailedTrace();
//
//		ExecutionConfiguration * failDueDataConfigTrace =
//				new ExecutionConfiguration(portCompRID,
//					StatementConstructor::newCode(
//						OperatorManager::OPERATOR_OUTPUT_ENV,
//						INCR_BF(aPort), newFreshList));
//
//		BFList newFreshTrace;
//
//		// keep the delays from iotrace in newFreshTrace and take off other infos
//		keepDelayOfTransition( childEC->getIOElementTrace(), newFreshTrace );
//
//		pChildECFail->getwExecutionData().setIOElementTrace(BF::REF_NULL);
//
//		for (const auto & bfDelta : newFreshTrace )
//		{
//			ExecutionDataFactory::appendIOElementTrace(pChildECFail->getwExecutionData(), bfDelta );
//		}
//
//		ExecutionDataFactory::appendIOElementTrace(pChildECFail->getwExecutionData(),
//				BF(failDueDataConfigTrace) );
//
//		// ajout nécessaire pour pouvoir effectuer simplement la projection
//		addRunnableTrace(pChildECFail, portCompRID);
//
//		pChildECFail->getwExecutionData().appendParameters( paramList );
//
//		//////////////////////////////////////////////////////////////
//		// Cette partie construit le Path Condition du FAIL
//		if ( childEC->getNodeCondition().isExpression() || paramsList.nonempty() )
//		{
//			BF nodeConditionFail = ExpressionConstructor::notExpr(childEC->getNodeCondition());
//
//			// get path condition from beginning to parent node anEC
//			BF PCParentEC = parentEC->getwExecutionData().getPathCondition();
//
//			pChildECFail->getwExecutionData().setNodeCondition(
//					ExpressionConstructor::orExpr(
//							nodeConditionFail,
//							notEqualityOnFreshVars));
//
//			// add evaluation of guard of transition leading to pChildECFail to path condition of
//			// node anEC (that is parent of pChildECFail)
//			pChildECFail->getwExecutionData().setPathCondition(
//					ExpressionConstructor::andExpr(
//							PCParentEC,
//							pChildECFail->getNodeCondition()));
//
//			listofECToAdd.append( pChildECFail );
//		}
//		//////////////////////////////////////////////////////////////
//	}
//}



//void DistributedTestCaseGeneratorProvider::createFailRemainingPortsInGraph(ExecutionContext * childEC,
//		ExecutionContext * parentEC,
//		InstanceOfPort * aRemainingPort, ListOfExecutionContext & listofECToAdd)
//{
//	ExecutionContext * pChildECFail = nullptr;
//
//	RuntimeID portCompRID = aRemainingPort->getRuntimeContainerRID();
//	AvmCode::OperandCollectionT newFreshList;
//	BFList paramList;
//
//	ENV.createNewFreshParam(portCompRID, *aRemainingPort, newFreshList, paramList);
//
//	pChildECFail = parentEC->cloneData(parentEC, true);
//
//	//////////////////////////////////////////////////////////////
//	// Cette partie désactive l'état actif de pChildEDFail, et
//	// faire de l'état mFailRID le nouvel état actif de pChildEDFail
//	ExecutionData & pChildEDFail = pChildECFail->getwExecutionData();
//
//	// Désactiver l'état actif de pChildEDFail i.e. --> ED( Example.s4 )
//	const AvmCode & scheduleCode = pChildEDFail.getRuntimeFormOnSchedule(mFailRID.getPRID()).to< AvmCode >();
//	pChildEDFail.mwsetRuntimeFormState(scheduleCode.operand(0).bfRID(), PROCESS_DISABLED_STATE);
//
//	// Faire de l'état mFailRID le nouvel état actif de pChildEDFail i.e. --> ED( Example.QUIESCENCE )
//	pChildEDFail.mwsetRuntimeFormOnScheduleAndIdle(mFailRID);
//	//////////////////////////////////////////////////////////////
//
//	// Create new instance of ExecutionCongtextFlags to replace old flags
//	////////////////////////
//	const ExecutionContextFlags * flags = new ExecutionContextFlags();
//
//	pChildECFail->setFlags( * flags );
//	////////////////////////
//
//	pChildECFail->getwFlags().setObjectiveFailedTrace();
//
//	///////////////////////////
//	// NEW FRESH PORT PARAMETER
//	pChildECFail->getwExecutionData().appendParameters( paramList );
//
//	// SET IO TRACE
////	pChildECFail->getwExecutionData().setIOElementTrace(
////			BF( new ExecutionConfiguration(portCompRID,
////					StatementConstructor::newCode(
////							OperatorManager::OPERATOR_OUTPUT_ENV,
////							INCR_BF(aRemainingPort), newFreshList)) ) );
//	///////////////////////////
//
//	BFList newFreshTrace;
//
//	keepDelayOfTransition( childEC->getIOElementTrace(), newFreshTrace );
//
//	pChildECFail->getwExecutionData().setIOElementTrace(BF::REF_NULL);
//
//	for (const auto & bfDelta : newFreshTrace )
//	{
//		ExecutionDataFactory::appendIOElementTrace(pChildEDFail, bfDelta );
//	}
//
//	ExecutionConfiguration * failConfigTrace =
//			new ExecutionConfiguration(portCompRID,
//					StatementConstructor::newCode(
//							OperatorManager::OPERATOR_OUTPUT_ENV,
//							INCR_BF(aRemainingPort), newFreshList));
//
//	ExecutionDataFactory::appendIOElementTrace(pChildEDFail,
//			BF(failConfigTrace) );
//
//	// ajout nécessaire pour pouvoir effectuer simplement la projection
//	addRunnableTrace(pChildECFail, portCompRID);
//
//	BF PCParentEC = parentEC->getExecutionData().getPathCondition();
//	// get path condition from beginning to parent node anEC
//
//	pChildECFail->getwExecutionData().setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//
//	pChildECFail->getwExecutionData().setPathCondition(
//			ExpressionConstructor::andExpr(
//					PCParentEC,
//					pChildECFail->getNodeCondition()));
//
//	listofECToAdd.append( pChildECFail );
//}



void DistributedTestCaseGeneratorProvider::addQuiescenceDuetoDataInSpec(ExecutionContext * childEC,
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

void DistributedTestCaseGeneratorProvider::addQuiescenceDuetoTimeInSpec(ExecutionContext * childEC,
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

void DistributedTestCaseGeneratorProvider::deleteUnobservableDelays( ExecutionContext & anEC )
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



void DistributedTestCaseGeneratorProvider::specifyQuiescence( ExecutionContext & anEC )
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


void DistributedTestCaseGeneratorProvider::addECToListECWithFlags( const ExecutionContext & anEC )
{
	for( const auto & childEC : anEC.getChildContexts() )
	{
		mListECWithFlags.append(childEC);

		addECToListECWithFlags(* childEC);
	}
}


void DistributedTestCaseGeneratorProvider::generateTestCases( ExecutionContext & rootProjectionEC,
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


void DistributedTestCaseGeneratorProvider::createPassTransitionInTestCase(ExecutionContext * childEC,
		Transition * tranItm, Machine * parentState,
		Machine * passState, Machine * failState, Machine * inconcState,
		const BF & clockTestCase, BFList bSenForNewTran, BFList listInstDataVars,
		ListOfExecutionContext listECForInconc )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newfreshList;
	BFList paramList;
	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeReadingClock;
	bool readValueOfClock = false;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newfreshList, paramList);

	createNewVariables( newfreshList );

	// Create new itm state
	Machine * itmState = Machine::newState(
		mStateMachine, "q_itm_" + std::to_string(mIndexState),
		Specifier::STATE_SIMPLE_MOC);
	itmState->setUnrestrictedName(childEC->str_position());

	mStateMachine->saveOwnedElement(itmState);
	mIndexState++;

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
		RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				///////////////////////////////////////////////////////
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newfreshList );

				BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

				if ( readValueOfClock )
				{
					codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

					tranItm->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeReadingClock ));
				}
				else
				{
					tranItm->setStatement( action );
				}

				tranItm->setTarget( *itmState );

				parentState->saveOwnedElement( tranItm );
				/////////////////end of Code tranItm//////////////

				/*
				 * this code creates the transition for Pass
				 */
				Transition * newTranPass = new sep::Transition( *itmState );

				// construction of data guard
				BF dataGuard = childEC->getExecutionData().getDataByNameID("localPC");

				// add BSen in guardDataSecondTransition
				for (const auto & bSen : bSenForNewTran)
				{
					dataGuard = ExpressionConstructor::andExpr(
							dataGuard, bSen );
				}

				BFList paramsList = getParamsListOfPort(childEC->getIOElementTrace());

				// add identification guard (ID) in guardDataSecondTransition
				BF identificationOnFreshVars = createEqualityOnFreshVars(
						childEC, newfreshList, listInstDataVars, paramsList );

				dataGuard = ExpressionConstructor::andExpr(
						dataGuard, identificationOnFreshVars );

				/*
				 * This code determines list of variables non instantiated untill now
				 */
				// Get variables non instantiated in guardExpr
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( dataGuard,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( const auto & varInst : listInstDataVars )
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

				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					dataGuard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							dataGuard );
				}
				else
				{
					dataGuard = ExpressionConstructor::newExpr(
							dataGuard );
				}

				BFCode dataGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						dataGuard );
				////////////////////////////////////////////////////////////////



				// construction of time guard
				BF timedGuard = ExpressionConstructor::newExpr(
						childEC->getExecutionData().getDataByNameID("localPtC") );

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );
				////////////////////////////////////////////////////////////////


				if ( timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{

					newTranPass->setStatement( StatementConstructor::newCodeFlat(
							OperatorManager::OPERATOR_SEQUENCE,
							dataGuardBFCode, timedGuardBFCode) );
				}
				else if ( not timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{
					newTranPass->setStatement( dataGuardBFCode );
				}
				else if ( timedGuardBFCode.isExpression() && not dataGuardBFCode.isExpression() )
				{
					newTranPass->setStatement( timedGuardBFCode );
				}

				newTranPass->setTarget( *passState );

				itmState->saveOwnedElement( newTranPass );



				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

				BF pathConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				BF pathTimeConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				for ( const auto & anEC : listECForInconc )
				{
					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
					{
						if ( SolverFactory::isStrongSatisfiable(
								ExpressionConstructor::andExpr(
										childEC->getNodeCondition(),
										anEC->getNodeCondition() ) ) )
						{
							/*
							 * this code create inconc state due to data
							 */
							///////////////////////////////////////////////////////
							createInconcOutputForSamePortInTestCase( anEC, itmState,
									inconcState, failState, bSenForNewTran,
									listInstDataVars, newfreshList,
									pathConditionInconcs,
									pathTimeConditionInconcs );
							////////////////end of Code create inconc////////////////
						}

						mListOfTreatedECs.append( anEC );
					}
				}

				// this code create fail state due to data
				///////////////////////////////////////////////////////
				createFailDueToSpecifiedTransition( childEC, itmState,
						failState, bSenForNewTran, listInstDataVars, newfreshList,
						pathConditionInconcs,
						pathTimeConditionInconcs );
				////////////////end of Code create Fail////////////////



			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
			{

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
			{

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
	mMapOfStateAndBSen[passState] = bSenForNewTran;

	// Associate a state with its corresponding set of instantiated variables
	mMapOfStateAndDataVarsInst[passState] = listInstDataVars;
}

void DistributedTestCaseGeneratorProvider::createQuiescenceTransitionInTestCase(
		ExecutionContext * childEC,	Transition * newTranInconc,
		Machine * parentState, Machine * inconcState,
		Machine * failState, const BF & clockTestCase,
		BFList bSenForNewTran, BFList listInstVars )
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

			BF forallTimedGuard = childEC->getExecutionData().getDataByNameID("localPtC");

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
			BF dataGuard = childEC->getExecutionData().getDataByNameID("localPC");

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
			for (const auto & bSen : bSenForNewTran)
			{
				dataGuard = ExpressionConstructor::andExpr(
						dataGuard, bSen );
			}

			if ( listOfVarsNonInstantiated.size() > 0 )
			{
				dataGuard = ExpressionConstructor::existsExpr(
						listOfVarsNonInstantiated,
						dataGuard );
			}

			BFCode dataGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					dataGuard );


			// construction of time guard
			BF timedGuard = childEC->getExecutionData().getDataByNameID("localPtC");

			BFCode timedGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timedGuard );

			newTranInconc->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					dataGuardBFCode, timedGuardBFCode, action ) ) ;
		}

		newTranInconc->setTarget( *inconcState );

		parentState->saveOwnedElement( newTranInconc );
	}
}

void DistributedTestCaseGeneratorProvider::createInconcTransitionInTestCase(
		ExecutionContext * childEC,	Transition * tranItm,
		Machine * parentState, Machine * failState,
		Machine * inconcState, const BF & clockTestCase,
		BFList bSenForNewTran, BFList listInstDataVars,
		ListOfExecutionContext listECForInconc )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;

	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeReadingClock;
	bool readValueOfClock = false;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newFreshList, paramList);

	AvmCode::OperandCollectionT::iterator it = newFreshList.begin();
	while ( it != newFreshList.end() )
	{
		if ( (*it).to_ptr< InstanceOfData >()->hasTypedClockTime() )
		{
			it = newFreshList.erase( it );
		}
		else
		{
			++it;
		}
	}

	createNewVariables( newFreshList );

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

	if ( anInstanceOfPort->getwModifier().isDirectionOutput() )
	{
		RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if ( aRoutingData.valid() )
		{
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				// Create new itm state
				Machine * itmState = Machine::newState(
					mStateMachine, "q_itm_" + std::to_string(mIndexState),
					Specifier::STATE_SIMPLE_MOC);
				itmState->setUnrestrictedName(childEC->str_position());

AVM_OS_DEBUG << "itmState->str() : " <<  itmState->str() << std::endl;//TODO

				mStateMachine->saveOwnedElement(itmState);
				mIndexState++;

				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

				if ( readValueOfClock )
				{
					codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

					tranItm->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeReadingClock ));
				}
				else
				{
					tranItm->setStatement( action );
				}

				tranItm->setTarget( *itmState );

				parentState->saveOwnedElement( tranItm );
				/////////////////end of Code tranItm//////////////

				/*
				 * this code creates the transition for Inconc
				 */
				Transition * newTranInconc = new sep::Transition( *itmState );

				// construction of data guard
				BF dataGuard = childEC->getExecutionData().getDataByNameID("localPC");

				// add BSen to guardDataSecondTransition
				for ( const auto & bSen : bSenForNewTran)
				{
					dataGuard = ExpressionConstructor::andExpr(
							dataGuard, bSen );
				}

				BFList paramsList = getParamsListOfPort(childEC->getIOElementTrace());

				BF identificationOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// add identification (ID) to guardDataSecondTransition
				dataGuard = ExpressionConstructor::andExpr(
						dataGuard, identificationOnFreshVars );

				// Get variables non instantiated in guardDataSecondTransition
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( dataGuard,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( auto varInst : listInstDataVars )
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

				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					dataGuard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							dataGuard );
				}
				else
				{
					dataGuard = ExpressionConstructor::newExpr(
							dataGuard );
				}

				BFCode dataGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						dataGuard );
				////////////////////////////////////////////////////////////////



				// construction of time guard
				BF timedGuard = ExpressionConstructor::newExpr(
						childEC->getExecutionData().getDataByNameID("localPtC") );

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );
				////////////////////////////////////////////////////////////////

				if ( timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							dataGuardBFCode, timedGuardBFCode) );
				}
				else if ( not timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( dataGuardBFCode );
				}
				else if ( timedGuardBFCode.isExpression() && not dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( timedGuardBFCode );
				}

				newTranInconc->setTarget( *inconcState );

				itmState->saveOwnedElement( newTranInconc );



				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

				BF pathConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				BF pathTimeConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				for ( const auto & anEC : listECForInconc )
				{
					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
					{
						if ( SolverFactory::isStrongSatisfiable(
								ExpressionConstructor::andExpr(
										childEC->getNodeCondition(),
										anEC->getNodeCondition() ) ) )
						{
							/*
							 * this code create inconc state due to data
							 */
							///////////////////////////////////////////////////////
							createInconcOutputForSamePortInTestCase( anEC, itmState,
									inconcState, failState, bSenForNewTran,
									listInstDataVars, newFreshList,
									pathConditionInconcs,
									pathTimeConditionInconcs );
							////////////////end of Code create inconc////////////////
						}

						mListOfTreatedECs.append( anEC );
					}
				}

				// this code create fail state due to data
				///////////////////////////////////////////////////////
				createFailDueToSpecifiedTransition( childEC, itmState,
						failState, bSenForNewTran, listInstDataVars, newFreshList,
						pathConditionInconcs,
						pathTimeConditionInconcs );
				////////////////end of Code create Fail////////////////

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
			{

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
			{
				// Create new itm state
				Machine * itmState = Machine::newState(
					mStateMachine, "q_itm_" + std::to_string(mIndexState),
					Specifier::STATE_SIMPLE_MOC);
				itmState->setUnrestrictedName(childEC->str_position());

				mStateMachine->saveOwnedElement(itmState);
				mIndexState++;

				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

				if ( readValueOfClock )
				{
					codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

					tranItm->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeReadingClock ));
				}
				else
				{
					tranItm->setStatement( action );
				}

				tranItm->setTarget( *itmState );

				parentState->saveOwnedElement( tranItm );
				/////////////////end of Code tranItm//////////////


				/*
				 * this code creates the transition for Inconc
				 */
				Transition * newTranInconc = new sep::Transition( *itmState );

				// construction of data guard
				BF dataGuard = childEC->getExecutionData().getDataByNameID("localPC");

				// add BSen to guardDataSecondTransition
				for ( const auto & bSen : bSenForNewTran)
				{
					dataGuard = ExpressionConstructor::andExpr(
							dataGuard, bSen );
				}

				BFList paramsList = getParamsListOfPort(childEC->getIOElementTrace());

				BF identificationOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// add identification (ID) to guardDataSecondTransition
				dataGuard = ExpressionConstructor::andExpr(
						dataGuard, identificationOnFreshVars );

				// Get variables non instantiated in guardDataSecondTransition
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( dataGuard,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( auto varInst : listInstDataVars )
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

				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					dataGuard = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							dataGuard );
				}
				else
				{
					dataGuard = ExpressionConstructor::newExpr(
							dataGuard );
				}

				BFCode dataGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						dataGuard );
				////////////////////////////////////////////////////////////////



				// construction of time guard
				BF timedGuard = childEC->getExecutionData().getDataByNameID("localPtC");

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );
				////////////////////////////////////////////////////////////////

				if ( timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							dataGuardBFCode, timedGuardBFCode) );
				}
				else if ( not timedGuardBFCode.isExpression() && dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( dataGuardBFCode );
				}
				else if ( timedGuardBFCode.isExpression() && not dataGuardBFCode.isExpression() )
				{
					newTranInconc->setStatement( timedGuardBFCode );
				}

				newTranInconc->setTarget( *inconcState );

				itmState->saveOwnedElement( newTranInconc );



				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

				BF pathConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				BF pathTimeConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				for ( const auto & anEC : listECForInconc )
				{
					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
					{
						if ( SolverFactory::isStrongSatisfiable(
								ExpressionConstructor::andExpr(
										childEC->getNodeCondition(),
										anEC->getNodeCondition() ) ) )
						{
							/*
							 * this code create inconc state due to data
							 */
							///////////////////////////////////////////////////////
							createInconcOutputForSamePortInTestCase( anEC, itmState,
									inconcState, failState, bSenForNewTran,
									listInstDataVars, newFreshList,
									pathConditionInconcs,
									pathTimeConditionInconcs );
							////////////////end of Code create inconc////////////////
						}

						mListOfTreatedECs.append( anEC );
					}
				}

				// this code create fail state due to data
				///////////////////////////////////////////////////////
				createFailDueToSpecifiedTransition( childEC, itmState,
						failState, bSenForNewTran, listInstDataVars, newFreshList,
						pathConditionInconcs,
						pathTimeConditionInconcs );
				////////////////end of Code create Fail////////////////
			}
		}
	}
	else if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		RoutingData aRoutingData = AvmCommunicationFactory::searchInputRoutingData(
						childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_OUTPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				tranItm->setStatement( action );

				tranItm->setTarget( *inconcState );

				parentState->saveOwnedElement( tranItm );



				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

				for ( const auto & anEC : listECForInconc )
				{
					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
					{
						mListOfTreatedECs.append( anEC );
					}
				}
			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
			{

			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
			{

			}
		}
	}
}

void DistributedTestCaseGeneratorProvider::createFailForTimeInTestCase(ExecutionContext * childEC,
		Machine * newState,
		Transition * newTran, Machine * parentState, Machine * failState,
		const BF & clockTestCase, BFList bSenForNewTran, BFList listInstVars )
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



void DistributedTestCaseGeneratorProvider::createInconcOutputForSamePortInTestCase(
		ExecutionContext * childEC,
		Machine * itmState, Machine * inconcState, Machine * failState,
		BFList bSenForNewTran, BFList listInstDataVars,
		AvmCode::OperandCollectionT newFreshList,
		BF & pathConditionInconcs,
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
				childEC->getExecutionData().getDataByNameID("localPC") );

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
		for ( const auto & bSen : bSenForNewTran )
		{
			dataGuard = ExpressionConstructor::andExpr(
					dataGuard,
					bSen );
		}

		dataGuard = ExpressionConstructor::andExpr(
				dataGuard,
				equalityOnFreshVars );

		if ( listOfVarsNonInstantiated.empty() )
		{
			dataGuard = ExpressionConstructor::newExpr(
					dataGuard );
		}
		else
		{
			dataGuard = ExpressionConstructor::existsExpr(
					listOfVarsNonInstantiated, dataGuard );
		}

		if ( SolverFactory::isStrongSatisfiable( dataGuard ) )
		{
			BFCode action = StatementConstructor::newCode(
					OperatorManager::OPERATOR_INPUT,
					INCR_BF(anInstanceOfPort), varsOfPort );

			BFCode dataGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					dataGuard );

			Transition * newTranInconc = new sep::Transition( *itmState );

			newTranInconc->setStatement( dataGuardBFCode ) ;

			newTranInconc->setTarget( *inconcState );

			itmState->saveOwnedElement( newTranInconc );

			pathConditionInconcs = ExpressionConstructor::orExpr(
					pathConditionInconcs,
					dataGuard );

			if ( childEC->getExecutionData().getDataByNameID("localPtC").isExpression() )
			{
				BF timedGuard = ExpressionConstructor::newExpr(
						childEC->getExecutionData().getDataByNameID("localPtC") );

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );

				newTranInconc->setStatement( StatementConstructor::newCodeFlat(
						OperatorManager::OPERATOR_SEQUENCE,
						dataGuardBFCode, timedGuardBFCode) );

				pathTimeConditionInconcs = ExpressionConstructor::orExpr(
						pathTimeConditionInconcs,
						timedGuard );
			}
		}
	}
}




void DistributedTestCaseGeneratorProvider::createFailDueToSpecifiedTransition(
		ExecutionContext * childEC,
		Machine * itmState, Machine * failState,
		BFList bSenForNewTran, BFList listInstVars,
		AvmCode::OperandCollectionT newFreshList,
		BF & pathConditionInconcs,
		BF & pathTimeConditionInconcs )
{
	// Create not equality expression on fresh vars
	///////////////////////////////////////////////
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFList paramList;

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newFreshList, paramList);

	BF notEqualityOnFreshVars = createNotEqualityOnFreshVars(
			childEC, portCompRID, newFreshList, anInstanceOfPort );
	///////////////////////////////////////////////

	if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		// add PC of parent of childEC to dataGuard
		// (including not ID inside of negation of node condition)
		BF dataGuard = ExpressionConstructor::notExpr(
				childEC->getExecutionData().getDataByNameID("localPC") );

		// union of negation of pathConditionInconcs and dataGuard
		dataGuard = ExpressionConstructor::andExpr(
				dataGuard,
				pathConditionInconcs.notExpr() );

		// Get variables non instantiated in guardExpr
		AvmCode::OperandCollectionT listOfVarsNonInstantiated;
		getDataVarsNonInstantiatedInGuard( dataGuard,
				listOfVarsNonInstantiated );

		// This code erases a variable in listOfVarsNonInstantiated if this variable
		// becomes instantiated
		for ( const auto & varInst : listInstVars)
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

		// union of negation of BSen and dataGuard
		for ( const auto & bSen : bSenForNewTran )
		{
			dataGuard = ExpressionConstructor::orExpr(
					dataGuard,
					ExpressionConstructor::notExpr(bSen) );
		}

		// union of negation of equality expr and dataGuard
		dataGuard = ExpressionConstructor::orExpr(
				dataGuard,
				notEqualityOnFreshVars );

		if ( listOfVarsNonInstantiated.empty() )
		{
			dataGuard = ExpressionConstructor::newExpr( dataGuard );
		}
		else
		{
			dataGuard = ExpressionConstructor::forallExpr(
					listOfVarsNonInstantiated, dataGuard );
		}

		// add PC of parent of childEC to guardExpr
		// (including not ID inside of negation of node condition)
		BF timedGuard = ExpressionConstructor::notExpr(
				childEC->getExecutionData().getDataByNameID("localPtC") );

		timedGuard = ExpressionConstructor::andExpr(
				timedGuard,
				pathTimeConditionInconcs.notExpr() );

		if ( SolverFactory::isStrongSatisfiable( timedGuard ) &&
				not SolverFactory::isStrongSatisfiable( dataGuard ) )
		{
			Transition * newTranFail = new sep::Transition( *itmState );

			BFCode timeGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timedGuard );

			newTranFail->setStatement( timeGuardBFCode );

			newTranFail->setTarget( *failState );

			itmState->saveOwnedElement( newTranFail );
		}
		else if ( SolverFactory::isStrongSatisfiable( dataGuard ) &&
				not SolverFactory::isStrongSatisfiable( timedGuard ) )
		{
			Transition * newTranFail = new sep::Transition( *itmState );

			BFCode dataGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					dataGuard );

			newTranFail->setStatement( dataGuardBFCode ) ;

			newTranFail->setTarget( *failState );

			itmState->saveOwnedElement( newTranFail );
		}
		else if ( SolverFactory::isStrongSatisfiable( dataGuard ) &&
				SolverFactory::isStrongSatisfiable( timedGuard ) )
		{
			// Creation of first transition FAIL
			BFCode dataGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					dataGuard );

			BFCode timeGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timedGuard );

			// Creation of first transition FAIL due to both data and time
			Transition * newTranFailDueDataAndTime = new sep::Transition( *itmState );

			newTranFailDueDataAndTime->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					dataGuardBFCode,
					timeGuardBFCode ) ) ;

			newTranFailDueDataAndTime->setTarget( *failState );

			itmState->saveOwnedElement( newTranFailDueDataAndTime );





			// Creation of second transition FAIL due to data
			BFCode negTimeGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					ExpressionConstructor::notExpr( timedGuard ) );

			Transition * newTranFailDueData = new sep::Transition( *itmState );

			newTranFailDueData->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					dataGuardBFCode,
					negTimeGuardBFCode ) ) ;

			newTranFailDueData->setTarget( *failState );

			itmState->saveOwnedElement( newTranFailDueData );




			// Creation of third transition FAIL due to time
			BFCode negDataGuardCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_GUARD,
					ExpressionConstructor::notExpr( dataGuard ) );

			Transition * newTranFailDueTime = new sep::Transition( *itmState );

			newTranFailDueTime->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					negDataGuardCode,
					timeGuardBFCode ) ) ;

			newTranFailDueTime->setTarget( *failState );

			itmState->saveOwnedElement( newTranFailDueTime );
		}
	}
}

//void DistributedTestCaseGeneratorProvider::createFailTransitionForTimeInTestCaseBis(
//		ExecutionContext * childEC,
//		Machine * itmState, Machine * failState )
//{
//	RuntimeID & portCompRID = RuntimeID::REF_NULL;
//	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
//	BFList paramList;
//
//	if (anInstanceOfPort->getwModifier().isDirectionOutput())
//	{
//		if ( childEC->getNodeTimedCondition().isExpression() )
//		{
//			Transition * newTranFail = new sep::Transition( *itmState );
//
//			BF timedGuard = ExpressionConstructor::notExpr(
//					childEC->getExecutionData().getDataByNameID("localPtC") );
//
//			BFCode timedGuardBFCode = StatementConstructor::newCode(
//					OperatorManager::OPERATOR_TIMED_GUARD,
//					timedGuard );
//
//			newTranFail->setStatement( timedGuardBFCode );
//
//			newTranFail->setTarget( *failState );
//
//			itmState->saveOwnedElement( newTranFail );
//		}
//	}
//}

void DistributedTestCaseGeneratorProvider::createFailRemainingPortsInTestCase(
		InstanceOfPort * aRemainingPort, ExecutionContext * nextEC,
		Transition * tranItm, Machine * parentState, Machine * failState,
		BF pathTimedConditionTestPurpose,
		const BF & clockTestCase,
		BFList bSenForNewTran, BFList listInstDataVars, BFList listInstTimeVars,
		bool deterministicWithStimulation )
{
	const RuntimeID & portCompRID = aRemainingPort->getRuntimeContainerRID();
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;

	ENV.createNewFreshParam(portCompRID, *aRemainingPort, newFreshList, paramList);

	AvmCode::OperandCollectionT newFreshListWithoutClockTime;

	AVM_OS_DEBUG << "HERE 6n" << std::endl;//TODO

	for (const auto & freshVar : newFreshList)
	{
		if( (not freshVar.isBuiltinValue())
			&& ExpressionTypeChecker::isClockTime(freshVar) )
		{
			// NOTHING
		}
		else
		{
			newFreshListWithoutClockTime.append( freshVar );
		}
	}

	AVM_OS_DEBUG << "HERE 6p" << std::endl;//TODO

	createNewVariables(newFreshList);

	for ( const auto & varInst : newFreshList)
	{
		listInstDataVars.append( varInst );
	}

	BF delay = getDelayOfTransition( nextEC->getIOElementTrace() );

	AVM_OS_DEBUG << "HERE 6q" << std::endl;//TODO

	listInstTimeVars.append( delay );

	AVM_OS_DEBUG << "HERE 6r" << std::endl;//TODO

	if ( aRemainingPort->getwModifier().isDirectionOutput() )
	{
		AVM_OS_DEBUG << "HERE 6s" << std::endl;//TODO

		Machine * itmState = Machine::newState(
			mStateMachine, "q_itm_" + std::to_string(mIndexState),
			Specifier::STATE_SIMPLE_MOC);
		itmState->setUnrestrictedName(nextEC->str_position());

		mStateMachine->saveOwnedElement(itmState);

		// Creation of first transition having port
		BFCode action = StatementConstructor::newCode(
				OperatorManager::OPERATOR_INPUT,
				INCR_BF( aRemainingPort ), newFreshListWithoutClockTime );

		if ( deterministicWithStimulation )
		{
			// add pathTimedConditionTestPurpose to guardExpr
			BF timeGuard = ExpressionConstructor::newExpr( pathTimedConditionTestPurpose );

			timeGuard = ExpressionConstructor::andExpr(
					timeGuard,
					ExpressionConstructor::newExpr(
							OperatorManager::OPERATOR_LT, clockTestCase, delay ) );

			// Get variables non instantiated in guardExpr
			AvmCode::OperandCollectionT listOfTimeVarsNonInstantiated;
			getTimeVarsNonInstantiatedInGuard( timeGuard,
					listOfTimeVarsNonInstantiated );

			// This code erases a variable in listOfVarsNonInstantiated if this variable
			// becomes instantiated
			for ( const auto & varInst : listInstTimeVars )
			{
				AvmCode::OperandCollectionT::iterator it = listOfTimeVarsNonInstantiated.begin();
				while ( it != listOfTimeVarsNonInstantiated.end() )
				{
					if ( *it == varInst )
					{
						it = listOfTimeVarsNonInstantiated.erase( it );
					}
					else
					{
						++it;
					}
				}
			}
			//////////////////////////////////////////////////////////////////

			AVM_OS_DEBUG << "HERE 6t" << std::endl;//TODO

			if ( listOfTimeVarsNonInstantiated.size() > 0 )
			{
				timeGuard = ExpressionConstructor::existsExpr(
						listOfTimeVarsNonInstantiated,
						timeGuard );
			}
			else
			{
				timeGuard = ExpressionConstant::BOOLEAN_TRUE;
			}

			BFCode timeGuardBFCode = StatementConstructor::newCode(
					OperatorManager::OPERATOR_TIMED_GUARD,
					timeGuard );

			tranItm->setStatement( StatementConstructor::newCode(
					OperatorManager::OPERATOR_SEQUENCE,
					timeGuardBFCode,
					action ) ) ;
		}
		else
		{
			tranItm->setStatement( action ) ;
		}

		tranItm->setTarget( *itmState );

		parentState->saveOwnedElement( tranItm );


		// Creation of second transition Fail with two guards at true
		Transition * newTranFail = new sep::Transition( *itmState );

		BFCode dataGuardCodeForNewTranFail = StatementConstructor::newCode(
				OperatorManager::OPERATOR_GUARD,
				ExpressionConstant::BOOLEAN_TRUE);

		BFCode timeGuardCodeForNewTranFail = StatementConstructor::newCode(
				OperatorManager::OPERATOR_TIMED_GUARD,
				ExpressionConstant::BOOLEAN_TRUE);

		newTranFail->setStatement( StatementConstructor::newCode(
				OperatorManager::OPERATOR_SEQUENCE,
				dataGuardCodeForNewTranFail,
				timeGuardCodeForNewTranFail) ) ;

		newTranFail->setTarget( *failState );

		itmState->saveOwnedElement( newTranFail );

//		mStateMachine->saveOwnedElement(newState);
		mIndexState++;
	}
}

void DistributedTestCaseGeneratorProvider::createCoveredTransitionInTestCase(
		ExecutionContext * childEC,	Machine * newState, Transition * aTran,
		Machine * parentState, Machine * failState, Machine * inconcState,
		BF pathConditionTestPurpose, BF pathTimedConditionTestPurpose,
		const BF & clockTestCase, BFList OCond, BFList listInstDataVars, BFList listInstTimeVars,
		ListOfExecutionContext listECForInconc )
{
	RuntimeID & portCompRID = RuntimeID::REF_NULL;
	AvmCode::OperandCollectionT newFreshList;
	BFList paramList;
	InstanceOfPort * anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID);
	BFCode codeResettingClock;
	BFCode codeReadingClock;
	bool resetClock = false;
	bool readValueOfClock = false;

AVM_OS_DEBUG << "HERE 1" << std::endl;//TODO

	ENV.createNewFreshParam(portCompRID, *anInstanceOfPort, newFreshList, paramList);

	BF nodeCondition = childEC->getwExecutionData().getNodeCondition();

	AvmCode::OperandCollectionT varsOfPort = getTermListOfPort( childEC->getIOElementTrace() );

	for ( const auto & varInst : varsOfPort)
	{
		listInstDataVars.append( varInst );
	}

AVM_OS_DEBUG << "HERE 2" << std::endl;//TODO

	BF delay = getDelayOfTransition( childEC->getIOElementTrace() );

	// Add delay to the list of durations which have been instantiated
	listInstTimeVars.append( delay );

	// This code verifies whether we reset clock if childEC is an EC in mListECsToResetClock
	for ( const auto & anEC : mListECsToResetClock )
	{
		if ( anEC == childEC )
		{
			resetClock = true;
			break;
		}
		else
		{
			resetClock = false;
		}
	}
	///////////////////////////////////////////////////////////////////

AVM_OS_DEBUG << "HERE 3" << std::endl;//TODO


	// This code verifies whether we measure duration by clock of test case
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
		RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
				childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				createNewVariables(newFreshList);

				////////////////this code create intermediate state in case of input//////////////////////
				BFCode action = StatementConstructor::newCode(
						OperatorManager::OPERATOR_INPUT,
						INCR_BF(anInstanceOfPort), newFreshList );

				if ( resetClock && not readValueOfClock )
				{
					codeResettingClock = resettingClockTestCase(clockTestCase);

					aTran->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeResettingClock ));
				}
				else if ( not resetClock && readValueOfClock )
				{
					codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

					aTran->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeReadingClock ));
				}
				else if ( resetClock && readValueOfClock )
				{
					codeReadingClock = readingValueOfClockTestCase(clockTestCase, delay);

					codeResettingClock = resettingClockTestCase(clockTestCase);

					aTran->setStatement(StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							action, codeReadingClock, codeResettingClock ));
				}
				else
				{
					aTran->setStatement( action );
				}

				Machine * itmState = Machine::newState(
					mStateMachine, "q_itm_" + std::to_string(mIndexState),
					Specifier::STATE_SIMPLE_MOC);
				//itmState->setUnrestrictedName(childEC->str_position());

				mStateMachine->saveOwnedElement(itmState);

				aTran->setTarget( *itmState );

				parentState->saveOwnedElement( aTran );
				/////////////////////////////end of Code intermediate state//////////////////////////



				/////////////////this code creates the second transition/////////////////////////////
				Transition * newTranCovered = new sep::Transition( *itmState );

				// Conjoin node condition
				BF guardDataSecondTransition = childEC->getNodeCondition();

				// Conjoin PC of parent of childEC
				guardDataSecondTransition = ExpressionConstructor::andExpr(
						guardDataSecondTransition,
						childEC->getPrevious()->getPathCondition() );

				// Conjoin BSen
				for ( const auto & bSen : OCond)
				{
					guardDataSecondTransition = ExpressionConstructor::andExpr(
							guardDataSecondTransition, bSen );
				}

				BFList paramsList = getParamsListOfPort(childEC->getIOElementTrace());

				BF identificationOnFreshVars = createEqualityOnFreshVars(
						childEC, newFreshList, listInstDataVars, paramsList );

				// Conjoin identification (ID)
				guardDataSecondTransition = ExpressionConstructor::andExpr(
						guardDataSecondTransition, identificationOnFreshVars );

				// Get variables non instantiated in guardDataSecondTransition
				AvmCode::OperandCollectionT listOfVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( guardDataSecondTransition,
						listOfVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( auto varInst : listInstDataVars )
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
				////////////////////////////////////////////////////////////////


				if ( listOfVarsNonInstantiated.size() > 0 )
				{
					guardDataSecondTransition = ExpressionConstructor::existsExpr(
							listOfVarsNonInstantiated,
							guardDataSecondTransition );
				}
				else
				{
					guardDataSecondTransition = ExpressionConstructor::newExpr(
							guardDataSecondTransition );
				}

				BFCode existDataGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_GUARD,
						guardDataSecondTransition );

				ExecutionContext * nextEC = nullptr;

				if ( childEC->hasChildContext() )
				{
					for ( const auto & aChild : childEC->getChildContexts() )
					{
						if ( aChild->getFlags().hasCoverageElementTrace() ||
								aChild->getFlags().hasObjectiveAchievedTrace() )
						{
							nextEC = aChild;
						}
					}
				}

				BF timedGuard = ExpressionConstant::BOOLEAN_TRUE;

				if ( nextEC != nullptr )
				{
					BF delayNextEC = getDelayOfTransition( nextEC->getIOElementTrace() );

					timedGuard = ExpressionConstructor::existsExpr(
							delayNextEC,
							ExpressionConstructor::andExpr(
									nextEC->getPathTimedCondition(),
									ExpressionConstructor::newExpr(
										OperatorManager::OPERATOR_LTE,
										clockTestCase,
										delayNextEC ) ) );
				}
				else
				{
					timedGuard = ExpressionConstructor::newExpr(
							childEC->getPathTimedCondition() );
				}

				BFCode timedGuardBFCode = StatementConstructor::newCode(
						OperatorManager::OPERATOR_TIMED_GUARD,
						timedGuard );

				if ( timedGuard.isExpression() && existDataGuardBFCode.isExpression() )
				{
					newTranCovered->setStatement( StatementConstructor::newCode(
							OperatorManager::OPERATOR_SEQUENCE,
							existDataGuardBFCode, timedGuardBFCode) );
				}
				else if ( not timedGuard.isExpression() && existDataGuardBFCode.isExpression() )
				{
					newTranCovered->setStatement( existDataGuardBFCode );
				}
				else if ( timedGuard.isExpression() && not existDataGuardBFCode.isExpression() )
				{
					newTranCovered->setStatement( timedGuardBFCode );
				}


				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

				BF pathConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				BF pathTimeConditionInconcs = ExpressionConstant::BOOLEAN_FALSE;

				for ( const auto & anEC : listECForInconc )
				{
					if ( childECPort == getIOPort( anEC->getIOElementTrace() ) )
					{
						if ( SolverFactory::isStrongSatisfiable(
								ExpressionConstructor::andExpr(
										childEC->getNodeCondition(),
										anEC->getNodeCondition() ) ) )
						{

							// this code creates inconc state due to data
							///////////////////////////////////////////////////////
							createInconcOutputForSamePortInTestCase( anEC, itmState,
									inconcState, failState, OCond,
									listInstDataVars, newFreshList,
									pathConditionInconcs,
									pathTimeConditionInconcs );
							////////////////end of Code create inconc////////////////
						}

						mListOfTreatedECs.append( anEC );
					}
				}

				/*
				 * this code create fail state due to data
				 */
				///////////////////////////////////////////////////////
				createFailDueToSpecifiedTransition( childEC, itmState,
						failState, OCond,
						listInstDataVars, newFreshList,
						pathConditionInconcs,
						pathTimeConditionInconcs );
				////////////////end of Code create Fail////////////////


				// add identification (ID) to bSenForNewTran
				OCond.append(identificationOnFreshVars);

				newTranCovered->setTarget( *newState );

				mStateMachine->saveOwnedElement(newState);
				mIndexState++;

				itmState->saveOwnedElement( newTranCovered );
				/////////////end of Code second state//////////////
			}
		}
	}
	else if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		RoutingData aRoutingData = AvmCommunicationFactory::searchInputRoutingData(
						childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

		if (aRoutingData.valid())
		{
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				createNewVariables( varsOfPort );

				/*
				 * Create guard
				 */
				// add pathConditionTestPurpose to guardExpr
				BF guard = ExpressionConstructor::newExpr( pathConditionTestPurpose );

				// Get variables non instantiated in guardExpr
				AvmCode::OperandCollectionT listOfDataVarsNonInstantiated;
				getDataVarsNonInstantiatedInGuard( guard,
						listOfDataVarsNonInstantiated );

				// This code erases a variable in listOfVarsNonInstantiated if this variable
				// becomes instantiated
				for ( const auto & varInst : listInstDataVars )
				{
					AvmCode::OperandCollectionT::iterator it = listOfDataVarsNonInstantiated.begin();
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
				//////////////////////////////////////////////////////////////////

				// add formula 'cl = z' to guardExpr
				guard = ExpressionConstructor::andExpr(
						guard, ExpressionConstructor::newExpr(
						OperatorManager::OPERATOR_EQ,
						clockTestCase, delay ) );

				// add bSen to guardExpr
				for ( const auto & bSen : OCond)
				{
					guard = ExpressionConstructor::andExpr( guard, bSen );
				}

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


				InstanceOfPort * childECPort = getIOPort( childEC->getIOElementTrace() );

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

				AVM_OS_DEBUG << "HERE 5a" << std::endl;//TODO


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

				AVM_OS_DEBUG << "HERE 5b" << std::endl;//TODO

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

				AVM_OS_DEBUG << "HERE 5c" << std::endl;//TODO

				mStateMachine->saveOwnedElement(newState);
				mIndexState++;

				aTran->setTarget( *newState );

				parentState->saveOwnedElement( aTran );

				AVM_OS_DEBUG << "HERE 5d" << std::endl;//TODO


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

				AVM_OS_DEBUG << "HERE 5e" << std::endl;//TODO

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

	AVM_OS_DEBUG << "HERE 5f" << std::endl;//TODO

	// Associate EC with its corresponding state in test case in order to
	// determine parent of the state in test case
	std::pair<ExecutionContext *, Machine * > newPair;
	newPair.first = childEC;
	newPair.second = newState;
	mVectorOfECAndState.append(newPair);

	// Associate a state with its corresponding BSen
	mMapOfStateAndBSen[newState] = OCond;

	AVM_OS_DEBUG << "HERE 5g" << std::endl;//TODO

	// Associate a state with its corresponding set of instantiated variables
	mMapOfStateAndDataVarsInst[newState] = listInstDataVars;
	mMapOfStateAndTimeVarsInst[newState] = listInstTimeVars;
}


void DistributedTestCaseGeneratorProvider::createInconcUnderSpecifiedInTestCase(
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


void DistributedTestCaseGeneratorProvider::createBoundBForTestCase()
{
	const std::string BOUND_B = "B";

	mBoundB = mStateMachine->saveOwnedElement(
			new sep::Variable( mStateMachine,
				sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
				TypeManager::POS_RATIONAL, BOUND_B, BF::REF_NULL ) );
}


void DistributedTestCaseGeneratorProvider::createTransitionsInTestCase( ExecutionContext & anEC,
		Machine * inconcState, Machine * failState,
		Machine * passState, const BF & pathConditionTestPurpose,
		const BF & pathTimedConditionTestPurpose, const BF & clockTestCase )
{
	Machine * initialState;
	Transition * initialTransition;
	Machine * newState;
	ExecutionContext * nextEC = nullptr;

	Vector<InstanceOfPort *> tableOfOutputPorts;

	Vector<InstanceOfPort *> tableOfInputPorts;

	bool isInstantiatedListOfOutputPorts = false;

	Transition * newTran;
	Machine * parentState;
	BFList bSenForNewTran;
	BFList listInstDataVars;
	BFList listInstTimeVars;

	// the case of first EC
	if ( !anEC.hasPrevious() )
	{
		////////////////////////////////
		// Create the initial state and save it
		initialState = Machine::newState(
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

		// Associate a state with its corresponding BSen
		BFList bSen;
		bSen.append(ExpressionConstant::BOOLEAN_TRUE);
		mMapOfStateAndBSen[newState] = bSen;

		// Associate a state with its set of instantiated vars
		BFList listInstDataVars;
		mMapOfStateAndDataVarsInst[newState] = listInstDataVars;
		BFList listInstTimeVars;
		mMapOfStateAndTimeVarsInst[newState] = listInstTimeVars;
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
		AVM_OS_DEBUG << "HERE 7" << std::endl;//TODO

		/////////////////// This code creates new Port ///////////////////
		// newPort = true requires to create a new Port, and not otherwise
		bool newPort = true;

		Port * aPort = nullptr;

		RuntimeID & portCompRID = RuntimeID::REF_NULL;

		AvmCode::OperandCollectionT newFreshList;

		InstanceOfPort * anInstanceOfPort =
				getIOPort(childEC->getIOElementTrace(), portCompRID);

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

		AVM_OS_DEBUG << "HERE 8" << std::endl;//TODO


		////////////////////////////////
		// Create a new state and save it
		newState = Machine::newState(
				mStateMachine, "q_" + std::to_string(mIndexState),
				Specifier::STATE_SIMPLE_MOC);
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

				newTran->setUnrestrictedName( childEC->str_position() );

				bSenForNewTran = mMapOfStateAndBSen[pair.second];
				listInstDataVars = mMapOfStateAndDataVarsInst[pair.second];
				listInstTimeVars = mMapOfStateAndTimeVarsInst[pair.second];
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

		AVM_OS_DEBUG << "childEC tiep theo" << std::endl;//TODO

		if ( childEC->getFlags().hasObjectiveAchievedTrace() )
		{
AVM_OS_DEBUG << "childEC Pass : " << childEC->str() <<  std::endl;//TODO

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

			createPassTransitionInTestCase( childEC, newTran, parentState,
					passState, failState, inconcState, clockTestCase,
					bSenForNewTran, listInstDataVars, listECForInconc );
		}
		else if ( childEC->getFlags().hasObjectiveInconclusiveTrace() )
		{
AVM_OS_DEBUG << "childEC Inconc : " << childEC->str() <<  std::endl;//TODO

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

				createInconcTransitionInTestCase( childEC, newTran, parentState,
						failState, inconcState, clockTestCase,
						bSenForNewTran, listInstDataVars,
						listECForInconc );
			}
		}
		else if ( childEC->getFlags().hasCoverageElementTrace() )
		{
AVM_OS_DEBUG << "childEC Covered : " << childEC->str() << std::endl;//TODO

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

			createCoveredTransitionInTestCase( childEC, newState,
					newTran, parentState, failState, inconcState,
					pathConditionTestPurpose, pathTimedConditionTestPurpose,
					clockTestCase, bSenForNewTran,
					listInstDataVars, listInstTimeVars,
					listECForInconc );

			AVM_OS_DEBUG << "HERE 6" << std::endl;//TODO
		}
//		else if ( childEC->getFlags().hasObjectiveAbortedTrace() )
//		{
//AVM_OS_DEBUG << "childEC quiescence : " << childEC->str() <<  std::endl;//TODO
//
//			if ( childEC->getNodeCondition().isExpression() ||
//					childEC->getNodeTimedCondition().isExpression() )
//			{
//				createQuiescenceTransitionInTestCase( childEC, newTran,
//						parentState, inconcState, failState,
//						clockTestCase, bSenForNewTran, listInstDataVars );
//			}
//		}
		else if ( childEC->getFlags().hasObjectiveFailedTrace() )
		{
//			bool deterministicWithStimulation = false;
//
//			ListOfExecutionContext listNeightborECOfChildEC = childEC->getPrevious()->getChildContexts();
//
//			for ( const auto & anEC : listNeightborECOfChildEC )
//			{
//				InstanceOfPort * anInstancePort = getIOPort( anEC->getIOElementTrace() );
//
//				if ( anInstancePort != nullptr )
//				{
//					if ( getIOPort( anEC->getIOElementTrace() )->getwModifier().isDirectionInput() )
//					{
//						deterministicWithStimulation = true;
//
//						break;
//					}
//				}
//			}
//
//			createFailTransitionForRemainingPortsInTestCase( childEC, newTran, parentState,
//					failState, pathTimedConditionTestPurpose, clockTestCase,
//					bSenForNewTran, listInstDataVars, listInstTimeVars,
//					deterministicWithStimulation );
		}
		else if ( childEC->getFlags().hasObjectiveTimeoutTrace() )
		{
AVM_OS_DEBUG << "childEC Fail Due Time : " << childEC->str() <<  std::endl;//TODO

			createFailForTimeInTestCase(childEC, newState, newTran, parentState,
					failState, clockTestCase, bSenForNewTran, listInstDataVars );
		}
		else
		{
AVM_OS_DEBUG << "childEC Other : " << childEC->str() <<  std::endl;//TODO

			mStateMachine->saveOwnedElement(newState);
			mIndexState++;

			initialTransition->setTarget( *newState );

			//	 Associate EC with its corresponding state in test case in order to
			// determine parent of the state in test case
			std::pair<ExecutionContext *, Machine * > newPair;
			newPair.first = childEC;
			newPair.second = newState;
			mVectorOfECAndState.append(newPair);

			// Associate a state with its corresponding BSen
			BFList bSen;
			bSen.append(ExpressionConstant::BOOLEAN_TRUE);
			mMapOfStateAndBSen[newState] = bSen;

			// Associate a state with its corresponding BSen
			BFList instDataVars;
			mMapOfStateAndDataVarsInst[newState] = instDataVars;
			BFList instTimeVars;
			mMapOfStateAndTimeVarsInst[newState] = instTimeVars;
		}

		AVM_OS_DEBUG << "HERE 6a" << std::endl;//TODO

		// Get list of output ports in model
		if ( anInstanceOfPort != nullptr )
		{
			AVM_OS_DEBUG << "HERE 6b" << std::endl;//TODO

			if ( not isInstantiatedListOfOutputPorts )
			{
				getListOfOutputPorts( anInstanceOfPort, tableOfOutputPorts );

				isInstantiatedListOfOutputPorts = true;
			}

			AVM_OS_DEBUG << "HERE 6c" << std::endl;//TODO

			verifyTreatedOutputPortForFail(tableOfOutputPorts, anInstanceOfPort);

			AVM_OS_DEBUG << "HERE 6d" << std::endl;//TODO
		}

		// Determine nextEC
		if ( childEC->hasChildContext() )
		{
			nextEC = childEC;

			AVM_OS_DEBUG << "nextEC : " << nextEC->str() << std::endl;//TODO

			AVM_OS_DEBUG << "HERE 6e" << std::endl;//TODO
		}
	}

	AVM_OS_DEBUG << "HERE 6f" << std::endl;//TODO


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
					aPort = createNewPortForRemainingInstanceOfPort( listOfParams, aRemainingPort );

					createNewComRouteForRemainingInstanceOfPort( aRemainingPort, aPort );
				}

				for (const auto & pair : mVectorOfECAndState)
				{
					if ( nextEC->getPrevious() == pair.first )
					{
						parentState = pair.second;
						newTran = new sep::Transition( * parentState );
						bSenForNewTran = mMapOfStateAndBSen[pair.second];
						listInstDataVars = mMapOfStateAndDataVarsInst[pair.second];
						listInstTimeVars = mMapOfStateAndTimeVarsInst[pair.second];
					}
				}

				bool deterministicWithStimulation = false;

				ListOfExecutionContext listNeighborECOfNextEC =
						nextEC->getPrevious()->getChildContexts();

				for ( const auto & anEC : listNeighborECOfNextEC )
				{
					InstanceOfPort * anInstancePort = getIOPort( anEC->getIOElementTrace() );

					if ( anInstancePort != nullptr )
					{
						if ( getIOPort( anEC->getIOElementTrace() )->getwModifier().isDirectionInput() )
						{
							deterministicWithStimulation = true;

							break;
						}
					}
				}

				AVM_OS_DEBUG << "HERE 6m" << std::endl;//TODO

				if ( nextEC->getPrevious()->isnotRoot() )
				{
					createFailRemainingPortsInTestCase( aRemainingPort,
							nextEC, newTran, parentState, failState,
							pathTimedConditionTestPurpose, clockTestCase,
							bSenForNewTran, listInstDataVars, listInstTimeVars,
							deterministicWithStimulation );
				}
			}
		}

		createTransitionsInTestCase( *nextEC, inconcState, failState,
				passState, pathConditionTestPurpose,
				pathTimedConditionTestPurpose, clockTestCase );
	}
}

Port * DistributedTestCaseGeneratorProvider::createNewPort( ExecutionContext * anEC,
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
				if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
				{
					modifier.setDirectionOutput();
				}
				else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
				{
					modifier.setDirectionInput();
				}
				else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
				{
					modifier.setDirectionInput();
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

		if ( not varInstance.hasTypedClockTime() )
		{
			const BaseTypeSpecifier & typeSpecifier = varInstance.getTypeSpecifier();

			BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

			Variable * param = new sep::Variable( mStateMachine,
					sep::Modifier::PROPERTY_PARAMETER_MODIFIER,
					typeVar, "",
					 BF::REF_NULL );

			aPort->saveParameter( param );
		}
	}

	// Associate RID with its corresponding Port
	std::pair<Port *, InstanceOfPort * > newPair;
	newPair.first = aPort;
	newPair.second = anInstanceOfPort;
	mVectorOfPortAndRID.append(newPair);

	mStateMachine->saveOwnedElement( aPort );

	return aPort;
}

Port * DistributedTestCaseGeneratorProvider::createNewPortForRemainingInstanceOfPort(
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
			modifier.setDirectionOutput();
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

		if ( not varInstance.hasTypedClockTime() )
		{
			const BaseTypeSpecifier & typeSpecifier = varInstance.getTypeSpecifier();

			BF typeVar = INCR_BF( const_cast< BaseTypeSpecifier * >(& typeSpecifier) );

			Variable * param = new sep::Variable( mStateMachine,
					sep::Modifier::PROPERTY_PARAMETER_MODIFIER,
					typeVar, "",
					 BF::REF_NULL );

			aPort->saveParameter( param );
		}
	}

	// Associate RID with its corresponding Port
	std::pair<Port *, InstanceOfPort * > newPair;
	newPair.first = aPort;
	newPair.second = anInstanceOfPort;
	mVectorOfPortAndRID.append(newPair);

	mStateMachine->saveOwnedElement( aPort );

	return aPort;
}

void DistributedTestCaseGeneratorProvider::createNewComRoute(
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
			if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
			{
				comRoute = &(mConnector->appendComRoute(
						sep::Modifier::PROPERTY_OUTPUT_DIRECTION ));
			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_BUFFER_KIND )
			{
				comRoute = &(mConnector->appendComRoute(
						sep::Modifier::PROPERTY_INPUT_DIRECTION ));
			}
			else if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_MULTICAST_KIND )
			{
				comRoute = &(mConnector->appendComRoute(
						sep::Modifier::PROPERTY_INPUT_DIRECTION ));
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

void DistributedTestCaseGeneratorProvider::createNewComRouteForRemainingInstanceOfPort(
		InstanceOfPort * anInstanceOfPort,
		Port * aPort )
{
	sep::ComPoint comPoint;

	if (anInstanceOfPort->getwModifier().isDirectionInput())
	{
		sep::ComRoute & comRoute = mConnector->appendComRoute(
				sep::Modifier::PROPERTY_OUTPUT_DIRECTION );

		comPoint = comRoute.appendComPoint(mStateMachine, aPort);
	}
	else if (anInstanceOfPort->getwModifier().isDirectionOutput())
	{
		sep::ComRoute & comRoute = mConnector->appendComRoute(
				sep::Modifier::PROPERTY_INPUT_DIRECTION );

		comRoute.appendComPoint(mStateMachine, aPort);
	}
}

BF DistributedTestCaseGeneratorProvider::createNewTypesEnum(AvmCode::OperandCollectionT newFreshList)
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

void DistributedTestCaseGeneratorProvider::createClockForTestCase( BF delay )
{
	bool isDenseTimed = getConfiguration().getSpecification().getSpecifier().hasFeatureDenseTimed();

	TypeSpecifier timeType( TypeManager::newClockTime(TYPE_CLOCK_SPECIFIER,
			isDenseTimed ? TypeManager::URATIONAL : TypeManager::UINTEGER) );

	mClockTestCase = mStateMachine->saveOwnedElement(
			new sep::Variable( mStateMachine,
					sep::Modifier::PROPERTY_PRIVATE_MODIFIER,
					timeType, "cl_TC", BF::REF_NULL ) );
}

void DistributedTestCaseGeneratorProvider::createNewTimeVariables(BF delay)
{
	if ( delay.is<InstanceOfData>() )
	{
		bool newTimedVar = true;

		bool isDenseTimed = getConfiguration().getSpecification().getSpecifier().hasFeatureDenseTimed();

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


void DistributedTestCaseGeneratorProvider::createNewVariables(AvmCode::OperandCollectionT termsListOfPort)
{
	for ( const auto & var : termsListOfPort )
	{
		// newVar = false does not require to create a new variable, and not otherwise
		bool newVar = true;

		InstanceOfData * varInstance = var.to_ptr< InstanceOfData >();

		if ( not varInstance->hasTypedClockTime() )
		{
			const BaseTypeSpecifier & typeSpecifier = varInstance->getTypeSpecifier();

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
						newVar = true;
					}
					else
					{
						newVar = false;
						break;
					}
				}
			}
			else
			{
				mStateMachine->saveOwnedElement( newVariable );

				mListVariablesTestCase.append( newVariable );

				newVar = false;
			}

			if ( newVar )
			{
				mStateMachine->saveOwnedElement( newVariable );

				mListVariablesTestCase.append( newVariable );
			}
		}
	}
}

} /* namespace sep */
