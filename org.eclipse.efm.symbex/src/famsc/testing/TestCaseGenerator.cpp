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

#include "TestCaseGenerator.h"

#include <computer/ExecutionDataFactory.h>
#include <computer/primitive/AvmCommunicationFactory.h>
#include <famcore/queue/ExecutionQueue.h>
#include <famsc/testing/AbstractTestCaseGeneratorProvider.h>
#include <famsc/testing/DistributedTestCaseGeneratorProvider.h>
#include <famsc/testing/UnitaryTestCaseGeneratorProvider.h>
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
#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/Workflow.h>
#include <time.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/CompositePart.h>
#include <solver/api/SolverFactory.h>
using namespace std;

namespace sep
{

/**
 *
 *
	TestCaseGeneration 'Online Test Case Generation for configuration tests' {
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

bool TestCaseGenerator::configureImpl()
{
	const sep::CompositePart::TableOfMachine & tableOfMachines =
			getConfiguration().getSpecification().getCompositePart()->getMachines();

	if ( tableOfMachines.size() <= 1 )
	{
		mTestCaseFacet = new UnitaryTestCaseGeneratorProvider( *this );
	}
	else
	{
		mTestCaseFacet = new DistributedTestCaseGeneratorProvider( *this );
	}

	mConfigFlag = mTestCaseFacet->configure( getParameterWObject() );

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void TestCaseGenerator::reportDefault(OutStream & os) const
{
//	Workflow & mWorkflow;
	reportHeader(os, "TEST CASE GENERATION");
}


/**
 * preProcessing : Add transitions Fail
 */
bool TestCaseGenerator::preprocess()
{
	AVM_OS_COUT << "PreProcess method"<< std::endl;

	return true;
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////


/**
 * filteringInitialize
 */
//bool TestCaseGeneration::filteringInitialize()
//{
//	if( getExecutionQueue().getInitQueue().singleton() )
//	{
//		// clone EC0 to mRootTestCaseEC
//		mRootGraphTestCaseEC = getExecutionQueue().getInitQueue().first()->cloneData(nullptr, true);
//
//		// map mRootTestCaseEC to EC0 of graph of TP
//		mMapOfECToItsClone[ getExecutionQueue().getInitQueue().first() ] = mRootGraphTestCaseEC;
//
//		getConfiguration().appendExecutionTrace( mRootGraphTestCaseEC );
//
//		mTestCaseEC = mRootGraphTestCaseEC;
//
//		mRootTP = getExecutionQueue().getInitQueue().first();
//
//		return( true );
//	}
//
//	AVM_OS_COUT << "TestCaseGeneration require only one root Execution Context to process !" << std::endl;
//
//	return( false );
//}


/**
 * preFiltering
 */
bool TestCaseGenerator::prefilter(ExecutionContext & anEC)
{
//	AVM_OS_COUT << "prefilter test TestCaseGeneration"<< std::endl;

	return true;
}


/**
 * postFiltering
 * Every post filter has to implement this method
 *
 * Iterate the list of EC executed in ResultQueue
 */

//bool TestCaseGeneration::postfilter()
//{
//	AVM_OS_COUT << "postfilter test"<< std::endl;
//
//	bool isCoveredTransition = false;
//
//	mListOfECToErase.clear();
//
//	ecQueue = &( getExecutionQueue().getResultQueue() ); //ResultQueue contains elements that are executed
//
//	ecQueueIt = ecQueue->begin();
//	ecQueueItEnd = ecQueue->end();
//	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt) // Iterate the list of EC executed in ResultQueue
//	{
//		if( postfilter(* (*ecQueueIt)) ) // calls function postfilter with parameters to analyze child of ecQueueIt
//		{
//			isCoveredTransition = true;
//		}
//
//	}
//
//	if (isCoveredTransition){
//		mCurrentTraceIndex++;
//
//		if (mCurrentTraceIndex==mTPasTransitionSequence.size()) // if mCurrentTraceIndex is equal to mTestPurposeTrace.size(),
//			// i.e. we are in the last transition of test purpose, we have to stop the symbolic execution
//		{
//			getSymbexRequestManager().postRequestStop(this);
//		}
//
//		// Erase ECs for INCONC reason !
//		for( const auto & itEC : mListOfECToErase )
//		{
//			itEC->getPrevious()->removeChildContext( itEC );
//
//			// Destruction of the EC
//			getSymbexEventManager().postEventDestroyCtx( itEC );
//			sep::destroyElement( itEC );
//		}
//	}
//	else
//	{
//		AVM_OS_COUT << "Unfound EC for coverage of "
//				<< mTPasTransitionSequence[mCurrentTraceIndex].str() << std::endl;
//
//	}
//
//	return( getExecutionQueue().hasResult() );
//}


/**
 * postProcessing
 */
bool TestCaseGenerator::postprocess()
{
	return mTestCaseFacet->postprocess();
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
