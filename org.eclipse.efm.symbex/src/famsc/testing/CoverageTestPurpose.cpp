/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 June. 2018
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <computer/ExecutionDataFactory.h>
#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>
#include <fml/executable/ExecutableForm.h>
#include <sew/Workflow.h>
#include <sew/Configuration.h>
#include <famcore/queue/ExecutionQueue.h>
#include <fml/symbol/Symbol.h>
#include <fml/executable/InstanceOfPort.h>
#include <fml/infrastructure/System.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/expression/StatementConstructor.h>
#include <fml/runtime/ExecutionConfiguration.h>
#include <famcore/api/AbstractProcessorUnit.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <computer/primitive/AvmCommunicationFactory.h>
#include <famsc/testing/CoverageTestPurpose.h>
#include <famsc/testing/TestCaseHelper.h>
#include <famsc/testing/UnitaryTestCaseGeneratorProvider.h>
#include <fml/runtime/RuntimeQuery.h>

#include <fml/trace/TraceFactory.h>
#include <sew/SymbexControllerRequestManager.h>

using namespace std;

namespace sep
{

/**
 *
 *
	CoverageTestPurpose 'Coverage of Test Purpose' {
		// required queue strategy is 'ALL'
		Sequence [
			transition = "receiveInfo"
			transition = "sendReq"
			transition = "timeOut1"
			transition = "receiveInfo"
			transition = "sendReq"
			transition = "receiveNewPrice"
			transition = "confirmUpdatePrice"
			transition = "receiveReq"
			transition = "initItRoom"
			transition = "nextRoom"
			transition = "priceOK"
			transition = "nextDate"
			transition = "dateOK"
			transition = "holdResa"
			transition = "receiveStatus"
			transition = "badId"
			transition = "receiveAnswer"
		]
		projection [
			machine = "Central"
			machine = "Hotel"
		] // end projection
	}
 *
 *
 */


// Initialize static boolean variables mTimedModel and mDeterministic
bool TestCaseHelper::mTimedModel = false;

bool TestCaseHelper::mDeterministic = true;

bool TestCaseHelper::mSequenceCoverage = true;

TraceFilter TestCaseHelper::mProjection( "TestCaseHelper#Projection" );

BFList TestCaseHelper::mListOfInobservableDelays;


bool CoverageTestPurpose::configureImpl()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
						<< "Unexpected a <null> TestCaseGeneration WObject !!!"
						<< SEND_EXIT;

	if ( getConfiguration().getSpecification().getSpecifier().hasFeatureTimed() )
	{
		mTimedModel = true;
	}

	///////////////////////////////////////////////////////////////////////////
	// Configuration of Test Purpose as Sequence of transitions
	const WObject * configTPasSequence = Query::getWSequence(
			getParameterWObject(), "Sequence");

	if( configTPasSequence == WObject::_NULL_ )
	{

	}

	TraceFactory traceFactory(this->getConfiguration(),
			ENV, getParameterWObject(), ExecutableForm::nullref());

	if( traceFactory.configure(configTPasSequence, & mTPasSequence) )
	{
		AVM_OS_COUT<< "traceFactory.configure : true";
	}

	AVM_OS_COUT << "Configuration of mTPasSequence: " << std::endl;
	mTPasSequence.toStream( AVM_OS_COUT << AVM_TAB_INDENT );

	if( mTPasSequence.hasOperand() )
	{
		mCurrentTraceIndex = 0;
	}
	else
	{
		AVM_OS_WARN << "Missing 'Sequence' parameters" << std::endl;
		mConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	// Configuration of CoverageTestPurpose
	mConfigFlag = mProjection.configure(
			ENV, getParameterWObject(), "projection", "PROJECTION")
			&& mConfigFlag;

	AVM_OS_COUT << "Configuration of PROJECTION: " << std::endl;
	mProjection.toStream( AVM_OS_COUT << AVM_TAB_INDENT );
	AVM_OS_COUT << END_INDENT << std::endl;

	if (! mProjection.hasMachinePoint())
	{
		AVM_OS_WARN << "Missing 'Projection' parameters" << std::endl;
		mConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	const WObject * propertySequence = Query::getWSequence(
			getParameterWObject(), "property");

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
		mConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	if (mConfigFlag){

		AVM_OS_DEBUG << "The parameters are correctly defined for CoverageTestPurpose..." << std::endl;

	}
	else {

		AVM_OS_DEBUG << "The parameters are not correctly defined for CoverageTestPurpose !" << std::endl;

	}

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void CoverageTestPurpose::reportDefault(OutStream & os) const
{
	reportHeader(os, "COVERAGE OF TEST PURPOSE");
}


/**
 * preProcessing
 */
bool CoverageTestPurpose::preprocess()
{
	AVM_OS_COUT << "PreProcess method" << std::endl;

	return true;
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////


/**
 * filteringInitialize
 */
bool CoverageTestPurpose::filteringInitialize()
{
	if( getExecutionQueue().getInitQueue().singleton() )
	{
		mRootOfGraphBeforeProjection =
				getExecutionQueue().getInitQueue().first();

		return( true );
	}

	return( false );
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////

/**
 * preFiltering
 */
bool CoverageTestPurpose::prefilter(ExecutionContext & anEC)
{
	return true;
}


/**
 * postFiltering
 * Every post filter has to implement this method
 *
 * Iterate the list of EC executed in ResultQueue
 */

bool CoverageTestPurpose::postfilter()
{
	AVM_OS_COUT << "---------------------------------" << std::endl;//TODO
	AVM_OS_COUT << "postfilter CoverageTestPurpose"<< std::endl;

	bool isCoveredTransition = false;

	ecQueue = &( getExecutionQueue().getResultQueue() ); //ResultQueue contains elements that are executed

	ecQueueIt = ecQueue->begin();

	ecQueueItEnd = ecQueue->end();

	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt) // Iterate the list of EC executed in ResultQueue
	{
		if( postfilter(* (*ecQueueIt)) ) // calls function postfilter with parameters to analyze child of ecQueueIt
		{
			isCoveredTransition = true;
		}
	}

	if (isCoveredTransition)
	{
		mSequenceCoverage = true;

		mCurrentTraceIndex++;

		if (mCurrentTraceIndex==mTPasSequence.size()) // if mCurrentTraceIndex is equal to mTestPurposeTrace.size(),
			// i.e. we are in the last transition of test purpose, we have to stop the symbolic execution
		{
			getSymbexRequestManager().postRequestStop(this);
		}

	}
	else
	{
		mSequenceCoverage = false;

		AVM_OS_COUT << "Unfound EC for coverage of "
				<< mTPasSequence[mCurrentTraceIndex].str() << std::endl;
	}

	return( getExecutionQueue().hasResult() );
}

bool CoverageTestPurpose::postfilter(ExecutionContext & anEC)
{
	//	AVM_OS_DEBUG << "analyse : " ;
	//	anEC.traceMinimum(AVM_OS_DEBUG);

	bool isCoveredTransition = false;
	ExecutionContext * childEC;
	ecChildItEnd = anEC.end();

	InstanceOfPort * anInstanceOfPort = nullptr;

	pair<uint32_t, uint32_t> coordinationOfChildEC;

	BF guardsDataOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

	BF guardsTimedOutputTransitions = ExpressionConstant::BOOLEAN_FALSE;

	/*
	 * Our test purpose is characterized as a sequence of transition of system TP = tr_1 . tr_2 ... tr_n
	 *
	 * This loop 'for' analyzes next execution contexts, i.e. child of EC, the current execution context.
	 * This analysis, in our case, is to detect if it covers or not mTestPurposeTrace[mCurrentTraceIndex].
	 * The covered element will be colored in yellow and green (for the last element), the other elements
	 * will be colored in orange (for INCONC transitions - both inputs and outputs which are not covered
	 * elements).
	 *
	 */
	for( ecChildIt = anEC.begin() ; ecChildIt != ecChildItEnd ; ++ecChildIt )
	{
		childEC = (*ecChildIt);

		// verify if the transition mTPasSequence[mCurrentTraceIndex] is covered.
		if( mTraceChecker.isSat(*childEC,
				mTPasSequence[mCurrentTraceIndex].to_ptr<TracePoint>()) )
		{
			childEC->getwFlags().setCoverageElementTrace();  // Color in yellow the test purpose covered

			if (mCurrentTraceIndex==mTPasSequence.size()-1) // if mCurrentTraceIndex is equal to mTPasSequence.size(),
			// i.e. we are in the last transition of test purpose, we have to stop the symbolic execution
			{
				childEC->getwFlags().setObjectiveAchievedTrace(); // Color in green the last element of test purpose covered
			}

			childEC->addInfo(*this, mTPasSequence[mCurrentTraceIndex]); // add information about transition fired to EC

			isCoveredTransition = true;

			getExecutionQueue().appendAnteWaiting(childEC); // add childEC to AnteWaiting for next waiting queue

			mTPasSequence[mCurrentTraceIndex].toStream( AVM_OS_DEBUG << AVM_TAB_INDENT );// TODO

			AVM_OS_COUT << "---------------------------------" <<std::endl;//TODO
			AVM_OS_COUT << std::endl;//TODO

			verifyIncontrollablePath(childEC);
		}
		else
		{
			if ( childEC->hasPrevious() )
			{
				if ( childEC->getPrevious()->hasPrevious() )
				{
					childEC->getwFlags().setObjectiveInconclusiveTrace();
				}
			}
		}

		RuntimeID portCompRID;
		anInstanceOfPort = getIOPort(childEC->getIOElementTrace(), portCompRID); // get port of mTestCaseChildEC

		if (anInstanceOfPort != nullptr)
		{
			if ( anInstanceOfPort->getModifier().isDirectionOutput() )
			{
				RoutingData aRoutingData = AvmCommunicationFactory::searchOutputRoutingData(
						childEC->getExecutionData(), *anInstanceOfPort, portCompRID);

				if ( aRoutingData.valid() )
				{
					if ( aRoutingData.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND )
					{
						mListOfECWithOutputPort.append( childEC );
					}
				}
			}
		}
	}

	// If mDeterministic == true, we continue to check the deterministic of TIOSTS
//	if ( mDeterministic )
//	{
//		mDeterministic = checkDeterministic();
//	}

	mListOfECWithOutputPort.clear();

	return isCoveredTransition;
}

/**
 * postProcessing
 */
bool CoverageTestPurpose::postprocess()
{
	AVM_OS_COUT << "PostProcess method for CoverageTestPurpose"<< std::endl;

	ExecutionContext * rootProjectionEC = nullptr;

	for( const auto & projComponentFilter : mProjection.mainTracePointFiter.getOperands() )
	{
		rootProjectionEC = mRootOfGraphBeforeProjection->cloneGraph(nullptr, true);

		getConfiguration().appendExecutionTrace( rootProjectionEC );


		////////////////////////////////////////////////////////////////////////////
		// This part of code deletes ECs which are unobservable or does not belong to
		// the component in question
		projection( * rootProjectionEC, projComponentFilter );

		deleteECsAfterProjection();

//		synchronizeDelaysAfterProjection( * rootProjectionEC );
		////////////////////////////////////////////////////////////////////////////


		// Set the last EC for each localized test purpose to a Pass EC
		ExecutionContext * nextEC = rootProjectionEC;

		while ( nextEC->hasChildContext() )
		{
			bool foundLastCoverageEC = true;

			for( const auto & aChildEC : nextEC->getChildContexts() )
			{
				if ( aChildEC->getPrevious()->isnotRoot() )
				{
					if ( aChildEC->getwFlags().hasCoverageElementTrace() )
					{
						for( const auto & itChildEC : aChildEC->getChildContexts() )
						{
							if ( itChildEC->getwFlags().hasObjectiveInconclusiveTrace() )
							{
								foundLastCoverageEC = true;
							}
							else if ( itChildEC->getwFlags().hasCoverageElementTrace() )
							{
								foundLastCoverageEC = false;
								break;
							}
						}

						if ( foundLastCoverageEC )
						{
							// Create new instance of ExecutionCongtextFlags to replace old flags
							////////////////////////
							const ExecutionContextFlags * flags = new ExecutionContextFlags();

							aChildEC->setFlags( * flags );
							////////////////////////

							aChildEC->getwFlags().setObjectiveAchievedTrace();
						}

						nextEC = aChildEC;
					}
				}
				else
				{
					nextEC = aChildEC;
					foundLastCoverageEC = false;
				}
			}

			if ( foundLastCoverageEC ) break;
		}
		//////////////////////////////////////////////////////////////////////////


//		////////////////////////////////////////////////////////////////////////////
//		// after the suppression of ECs which are unobservable or does not belong to
//		// the component in question, the graph can contain transitions which share
//		// a same port from an EC, we need also to delete them
//		getECsHavingSamePortAfterProjection( * rootProjectionEC );
//
//		deleteECsHavingSamePortAfterProjection();
//		////////////////////////////////////////////////////////////////////////////
	}

	return true;
}


void CoverageTestPurpose::getECsHavingSamePortAfterProjection( ExecutionContext & anEC )
{
	mListECHavingSamePortAfterProjection.append( & anEC );

	for( const auto & itChildEC : anEC.getChildContexts() )
	{
		getECsHavingSamePortAfterProjection( * itChildEC );
	}
}


void CoverageTestPurpose::deleteECsHavingSamePortAfterProjection()
{
	ExecutionContext::rw_child_iterator it = mListECHavingSamePortAfterProjection.begin();

	ExecutionContext * anEC = nullptr;

	while ( it != mListECHavingSamePortAfterProjection.end() )
	{
		anEC = (*it);

		if ( !anEC->hasContainer() )
		{
			it++;
		}
		else
		{
			ExecutionContext * containerEC = anEC->getContainer();

			anEC->clearChildContext();

			containerEC->removeChildContext(anEC);

			it = mListECHavingSamePortAfterProjection.erase(it);
		}
	}
}


void CoverageTestPurpose::projection(ExecutionContext & anEC, BF projComponentFilter)
{
	InstanceOfPort * aPort = getIOPort( anEC.getIOElementTrace() );

	bool addNewDelay = true;

	if ( not mTraceChecker.isSat(anEC, projComponentFilter) )
	{
		anEC.getwExecutionData().setRunnableElementTrace(ExpressionConstant::STRING_EMPTY);

		anEC.getwExecutionData().setIOElementTrace(ExpressionConstant::STRING_EMPTY);

		mListECToDelete.append( & anEC );
	}
	else if ( aPort == nullptr && anEC.getPrevious()->isnotRoot() ) // case of UNOBSERVABLE ACTIONS
	{
		BF newDelay = getDelayOfTransition( anEC.getIOElementTrace() );

		anEC.getwExecutionData().setRunnableElementTrace(ExpressionConstant::STRING_EMPTY);

		anEC.getwExecutionData().setIOElementTrace(ExpressionConstant::STRING_EMPTY);

		mListECToDelete.append( & anEC );

		for( const auto & addedDelay : mListOfInobservableDelays )
		{
			if ( addedDelay == newDelay )
			{
				addNewDelay = false;
				break;
			}
		}
		if ( addNewDelay ) mListOfInobservableDelays.append( newDelay );
	}

	for( const auto & itChildEC : anEC.getChildContexts() )
	{
		projection( * itChildEC, projComponentFilter );
	}
}


void CoverageTestPurpose::synchronizeDelaysAfterProjection( ExecutionContext & anEC )
{
	ExecutionContext * nextEC = nullptr;

	if ( anEC.isnotRoot() )
	{
		ListOfExecutionContext listChildECs = anEC.getChildContexts();

		ExecutionContext::rw_child_iterator it = listChildECs.begin();

		BF delayReference;

		BFList newFreshTrace;

		while ( it != listChildECs.end() )
		{
			if ( (*it)->getFlags().hasCoverageElementTrace() ||
					(*it)->getFlags().hasObjectiveAchievedTrace()	)
			{
				keepDelayOfTransition( (*it)->getIOElementTrace(), newFreshTrace );

				// set delay of covered transition as the delay of reference
				delayReference = getDelayOfTransition( (*it)->getIOElementTrace() );

				nextEC = *it;

				it = listChildECs.erase( it );
			}
			else
			{
				++it;
			}
		}

		for ( const auto & otherChild : listChildECs )
		{
			otherChild->getwExecutionData().setIOElementTrace( BF::REF_NULL );

//			ExecutionDataFactory::appendIOElementTrace( otherChild->getwExecutionData(), delayReference );

			for (const auto & bfDelta : newFreshTrace )
			{
				ExecutionDataFactory::appendIOElementTrace( otherChild->getwExecutionData(), bfDelta );
			}
		}
	}
	else if ( anEC.isRoot() )
	{
		for ( const auto & aChild : anEC.getChildContexts() )
		{
			nextEC = aChild;
		}
	}

	if ( nextEC != nullptr )
	synchronizeDelaysAfterProjection( * nextEC );
}


void CoverageTestPurpose::deleteECsAfterProjection()
{
	ExecutionContext::rw_child_iterator it = mListECToDelete.begin();

	ExecutionContext * tmpEC = nullptr;

	ListOfExecutionContext listOfECToAppendAsChildsOfParentEC;

	while ( it != mListECToDelete.end() )
	{
		tmpEC = (*it);

		if ( !tmpEC->hasContainer() )
		{
			it++;
		}
		else
		{
			ExecutionContext * parentTmpEC = tmpEC->getContainer();

			for ( const auto & childEC : tmpEC->getChildContexts() )
			{
				listOfECToAppendAsChildsOfParentEC.append( childEC );

				childEC->setContainer(nullptr);
			}

			tmpEC->clearChildContext();

			parentTmpEC->removeChildContext(tmpEC);

			it = mListECToDelete.erase(it);

			getSymbexEventManager().notifyEventDestroyCtx( tmpEC );

			sep::destroyElement( tmpEC );

			if ( listOfECToAppendAsChildsOfParentEC.size() > 0 )
			{
				for ( const auto & childEC : listOfECToAppendAsChildsOfParentEC )
				{
					parentTmpEC->appendChildContext( childEC );


//					bool duplicateEC = false;
//
//					InstanceOfPort * portChildEC = getIOPort( childEC->getIOElementTrace() );
//
//					if ( childEC->getwFlags().hasCoverageElementTrace() ||
//							childEC->getwFlags().hasObjectiveAchievedTrace() )
//					{
//						parentTmpEC->appendChildContext( childEC );
//					}
//					else
//					{
//						for ( const auto & anEC : childsOfParentTmpEC )
//						{
//							InstanceOfPort * portAnEC = getIOPort( anEC->getIOElementTrace() );
//
//							if ( portAnEC->getwModifier().isDirectionInput() )
//							{
//								if ( portAnEC->isEQ( portChildEC )
//										&& anEC->getPathCondition().isEQ( childEC->getPathCondition() )
//										&& anEC->getPathTimedCondition().isEQ( childEC->getPathTimedCondition() ) )
//								{
////									AVM_OS_DEBUG << anEC->str() << " anEC->getIOElementTrace() : " <<
////											anEC->getIOElementTrace() << std::endl;//TODO
////									AVM_OS_DEBUG << childEC->str() << " childEC->getIOElementTrace() : " <<
////											childEC->getIOElementTrace() << std::endl;//TODO
//									duplicateEC = true;
//									break;
//								}
//							}
//						}
//
//						if ( not duplicateEC )
//						{
//							parentTmpEC->appendChildContext( childEC );
//						}
//					}
				}

				listOfECToAppendAsChildsOfParentEC.clear();
			}
		}

		/////////////////////////////////////////////////////////////////////////////
		// This code deletes ECs which have been already deleted, and so we could not
		// access them lately
//		ExecutionContext::rw_child_iterator itNew = mListOfECToAddInProjection.begin();
//
//		ExecutionContext * tmpECNew = nullptr;
//
//		while ( itNew != mListOfECToAddInProjection.end() )
//		{
//			tmpECNew = (*itNew);
//
//			if ( tmpECNew == tmpEC )
//			{
//				itNew = mListOfECToAddInProjection.erase( itNew );
//			}
//			else
//			{
//				itNew++;
//			}
//		}
		/////////////////////////////////////////////////////////////////////////////
	}
}




}
