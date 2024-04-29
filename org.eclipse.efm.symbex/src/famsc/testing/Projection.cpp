/*
 * Projection.cpp
 *
 *  Created on: 13 sept. 2017
 *      Author: NN245105
 */

#include "Projection.h"

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
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>

#include <fml/trace/TraceFactory.h>
#include <sew/SymbexControllerRequestManager.h>

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
			//transition = "ReturnCash"
			transition = "InsufBalance"
			// TP2
			//transition = "ReturnCash"
			//transition = "ReturnCash"
			//transition = "InsufBalance"
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

bool Projection::configureImpl()
{

	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
						<< "Unexpected a <null> TestCaseGeneration WObject !!!"
						<< SEND_EXIT;

	///////////////////////////////////////////////////////////////////////////
	// Configuration of Test Purpose as Sequence of transitions
	const WObject * configTPasTransitionSequence = Query::getWSequence(
			getParameterWObject(), "TPasTransitionSequence");

	if( configTPasTransitionSequence == WObject::_NULL_ )
	{

	}

	TraceFactory traceFactory(this->getConfiguration(),
			ENV, getParameterWObject(), ExecutableForm::nullref());

	if( traceFactory.configure(configTPasTransitionSequence, & mTPasTransitionSequence) )
	{
		AVM_OS_COUT<< "traceFactory.configure : true";
	}

//	mConfigFlag = mTestPurposeTrace.configure(
//			ENV, getParameterWObject(), "testpurpose", "TESTPURPOSE")
//			&& mConfigFlag;

	AVM_OS_COUT << "Configuration of TPasTransitionSequence: " << std::endl;
	mTPasTransitionSequence.toStream( AVM_OS_COUT << AVM_TAB_INDENT );

	if( mTPasTransitionSequence.hasOperand() )
	{
		mCurrentTraceIndex = 0;
	}
	else
	{
		AVM_OS_WARN << "Missing 'TPasTransitionSequence' parameters" << std::endl;
		mConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	// Configuration of Sequence of input and output actions
	const WObject * configIOSequence = Query::getWSequence(
			getParameterWObject(), "IOSequence");

	if( configIOSequence == WObject::_NULL_ )
	{

	}

	if( traceFactory.configure(configIOSequence, & mIOSequence) )
	{
		AVM_OS_COUT<< "traceFactory.configure : true";
	}

	AVM_OS_COUT << "Configuration of mIOSequence: " << std::endl;
	mIOSequence.toStream( AVM_OS_COUT << AVM_TAB_INDENT );

	if( mIOSequence.hasOperand() )
	{
		mCurrentTraceIndex = 0;
	}
	else
	{
		AVM_OS_WARN << "Missing 'IOSequence' parameters" << std::endl;
		mConfigFlag = false;
	}
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	// Configuration of PRESERVED
	const WObject * configPRESERVEDSequence = Query::getWSequence(
			getParameterWObject(), "PRESERVED");

	if( configPRESERVEDSequence == WObject::_NULL_ )
	{

	}

	if( traceFactory.configure(configPRESERVEDSequence, & mPRESERVED) )
	{
		AVM_OS_COUT<< "traceFactory.configure : true";
	}

	AVM_OS_COUT << "Configuration of PRESERVED: " << std::endl;
	mPRESERVED.toStream( AVM_OS_COUT << AVM_TAB_INDENT );
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	// Configuration of QUIESCENCE
	const WObject * configQUIESCENCESequence = Query::getWSequence(
			getParameterWObject(), "QUIESCENCE");

	if( configQUIESCENCESequence == WObject::_NULL_ )
	{

	}

	if( traceFactory.configure(configQUIESCENCESequence, & mQUIESCENCE) )
	{
		AVM_OS_COUT<< "traceFactory.configure : true";
	}

	AVM_OS_COUT << "Configuration of QUIESCENCE: " << std::endl;
	mQUIESCENCE.toStream( AVM_OS_COUT << AVM_TAB_INDENT );
	///////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////////////////////////////////////////
	// Configuration of Projection
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


	if (mConfigFlag){

		AVM_OS_LOG << "The parameters are correctly defined" << "\n";

	}
	else {

		AVM_OS_WARN << "The parameters are not correctly defined" << "\n";
	}

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void Projection::reportDefault(OutStream & os) const
{
//	Workflow & mWorkflow;
	reportHeader(os, "TEST CASE GENERATION ");

	os << EMPHASIS("EVERY THING IS OK", '=', 80);

//	mWorkflow=getConfiguration().getWorkflow();
//	cout << "getConfiguration().getWorkflow() : " << mWorkflow.toString() << std::endl;

}


/**
 * preProcessing : Add transitions Fail
 */
bool Projection::preprocess()
{
	AVM_OS_COUT << "PreProcess method"<< std::endl;

	return true;
}


////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////

/**
 * preFiltering
 */
bool Projection::prefilter(ExecutionContext & anEC)
{
	AVM_OS_COUT << "prefilter test"<< std::endl;

	return true;
}


/**
 * postFiltering
 * Every post filter has to implement this method
 *
 * Iterate the list of EC executed in ResultQueue
 */

bool Projection::postfilter()
{

	AVM_OS_COUT << "postfilter test"<< std::endl;

	bool isCoveredTransition = false;
	ecQueue = &( getExecutionQueue().getResultQueue() ); //ResultQueue contains elements that are executed
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt) // Iterate the list of EC executed in ResultQueue
	{
		if(  postfilter(* (*ecQueueIt)) ) // calls function postfilter with parameters to analyze child of ecQueueIt
		{
			isCoveredTransition = true;
		}

	}

	if (isCoveredTransition){
		mCurrentTraceIndex++;

		if (mCurrentTraceIndex==mTPasTransitionSequence.size()) // if mCurrentTraceIndex is equal to mTestPurposeTrace.size(),
			// i.e. we are in the last transition of test purpose, we have to stop the symbolic execution
		{
			getSymbexRequestManager().postRequestStop(this);
		}

	}
	else{
		AVM_OS_COUT << "Unfound EC for coverage of "
				<< mTPasTransitionSequence[mCurrentTraceIndex].str() << std::endl;
		// TODO in case it could not find
	}

	return( getExecutionQueue().hasResult() );
}

bool Projection::postfilter(ExecutionContext & anEC)
{
	AVM_OS_COUT << "analyse : " ;
	anEC.traceMinimum(AVM_OS_COUT);

	bool isCoveredTransition = false;
	ExecutionContext * childEC;
	ecChildItEnd = anEC.end();

	/*
	 * Our test purpose is characterized as a sequence of transition of system TP = tr_1 . tr_2 ... tr_n
	 *
	 * This loop 'for' analyzes next execution contexts, i.e. child of EC, the current execution context.
	 * This analysis, in our case, is to detect if it covers or not mTestPurposeTrace[mCurrentTraceIndex].
	 *
	 */
	for( ecChildIt = anEC.begin() ; ecChildIt != ecChildItEnd ;  )
	{
		childEC = (*ecChildIt);

		if( mTraceChecker.isSat(*childEC,
				mIOSequence[mCurrentTraceIndex].to<TracePoint>()) ) // verify if the input or output
			// in mTestIOSequence[mCurrentTraceIndex] is covered. The method isSat is used not only for transitions,
			// but also for signals input and output.
		{
			if( mTraceChecker.isSat(*childEC,
					mTPasTransitionSequence[mCurrentTraceIndex].to<TracePoint>()) ) // verify if the transition
				// mTestTransitionSequence[mCurrentTraceIndex] is covered. Note : Our TP is sequence of transitions
			{
				++ecChildIt; // We preserve this node because it is in TP

				childEC->getwFlags().setCoverageElementTrace(); // Color in yellow the test purpose covered

				if (mCurrentTraceIndex==mTPasTransitionSequence.size()-1) // if mCurrentTraceIndex is equal to mTPasTransitionSequence.size(),
				// i.e. we are in the last transition of test purpose, we have to stop the symbolic execution
				{
					childEC->getwFlags().setObjectiveAchievedTrace(); // Color in green the last element of test purpose covered
				}

				childEC->addInfo(*this, mTPasTransitionSequence[mCurrentTraceIndex]); // add information about transition fired to EC

				isCoveredTransition = true;

				getExecutionQueue().appendAnteWaiting(childEC); // add childEC to AnteWaiting for next waiting queue

				AVM_OS_COUT << "found transition "<< std::endl;

				mTPasTransitionSequence[mCurrentTraceIndex].toStream( AVM_OS_COUT << AVM_TAB_INDENT );

//				if (mTPasTransitionSequence[mCurrentTraceIndex].str()){
//
//				}

				AVM_OS_COUT << TAB << "childEC->getRunnableElementTrace() : " << childEC->getRunnableElementTrace().str() << std::endl;

				AVM_OS_COUT << TAB << "childEC->getwExecutionData() : " << childEC->getwExecutionData().str() << std::endl;

//				AVM_OS_COUT << TAB << "childEC->getwExecutionData() : " << childEC->getwExecutionData().getSystemRID().get << std::endl;

				AVM_OS_COUT << TAB << "childEC->getExecutionData() : " << childEC->getExecutionData().getSystemRID().str() << std::endl;

				AVM_OS_COUT << TAB << "childEC->getwExecutionData() : " << childEC->getwExecutionData().getRID().str() << std::endl;

//				childEC->getwExecutionData().getSystemR;

//				AVM_OS_COUT << TAB << "childEC->getwExecutionData() : " << childEC->getwExecutionData().getNa.str() << std::endl;



			}
			else
			{
				++ecChildIt; // We preserve this node for verdict INCONC

				childEC->getwFlags().setObjectiveAbortedTrace(); // Color in orange the paths that have same IO as TP
				// but these paths are not TP

				if (mCurrentTraceIndex==mIOSequence.size()-1) // if mCurrentTraceIndex is equal to mIOSequence.size(),
				// we stop process
				{
					childEC->getwFlags().setObjectiveAbortedTrace(); // Color in orange the last elements of paths
				}

				childEC->addInfo(*this, mIOSequence[mCurrentTraceIndex]); // add information about transition fired to EC

				isCoveredTransition = true;

				getExecutionQueue().appendAnteWaiting(childEC); // add childEC to AnteWaiting for next waiting queue

				AVM_OS_COUT << "found IO "<< std::endl;

				mIOSequence[mCurrentTraceIndex].toStream( AVM_OS_COUT << AVM_TAB_INDENT );
			}

		}
//		else if(  mTraceChecker.isSat(*childEC,	mPRESERVED) )
//		{
//			ecChildIt = anEC.eraseChildContext(ecChildIt); // We do not preserve this node for verdict Fail
//		}
		else if( mTraceChecker.isSat(*childEC,	mQUIESCENCE) )
		{

			++ecChildIt; // We preserve this node for verdict INCONC and we point to the next node

		}
		else
		{
			++ecChildIt; // We preserve this node for verdict INCONC and we point to the next node
		}
	}

	return isCoveredTransition;
}

/**
 * postProcessing
 */
bool Projection::postprocess()
{
	AVM_OS_COUT << "PostProcess method"<< std::endl;

	const ExecutionContext & rootEC = getConfiguration().getFirstExecutionTrace();

	AVM_OS_COUT << "rootEC.traceMinimum "<<  std::endl;

	rootEC.traceMinimum(AVM_OS_COUT);

	ExecutionContext * rootProjectionEC = rootEC.cloneGraph(nullptr, true);

//	ExecutionContext * pChildEC; // create new Node
//
//	pChildEC = rootEC->cloneNode(true);
//
//	pChildEC->getwExecutionData().setRunnableElementTrace(ExpressionConstant::STRING_EMPTY);
//
//	BF pathConditionRootEC = rootEC->getExecutionData().getPathCondition();
//	// get path condition from beginning to parent node rootEC
//
//	pChildEC->setContainer(rootEC); // add rootEC as parent of pChildEC
//
//	pChildEC->getwExecutionData().setNodeCondition( ExpressionConstant::BOOLEAN_TRUE );
//
//	pChildEC->getwExecutionData().setPathCondition(
//			ExpressionConstructor::andExpr(
//					pathConditionRootEC,
//					pChildEC->getNodeCondition()));

	for( const auto & var : rootProjectionEC->getChildContexts() )
	{
		AVM_OS_COUT << TAB << "rootProjectionEC->getChildContexts() : " << var->str() << std::endl;
		rootProjectionEC->getChildContexts();
	}

	getConfiguration().appendExecutionTrace( rootProjectionEC );

	for( const auto & var : getConfiguration().getExecutionTrace() )
	{
		AVM_OS_COUT << TAB << "getConfiguration().getExecutionTrace() : " << var->str() << std::endl;
	}



//	rootProjectionEC;

//	const std::string aNameID = "";

//	System testCaseSystem = new System(aNameID);

	return true;
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
