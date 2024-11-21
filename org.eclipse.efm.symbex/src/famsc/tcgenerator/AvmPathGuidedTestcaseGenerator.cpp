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

#include "AvmLabelledTestCaseFactory.h"
#include "AvmTestCaseFactory.h"

#include <builder/Builder.h>

#include <collection/Typedef.h>

#include <famcore/queue/ExecutionQueue.h>
#include <famsc/tcgenerator/AvmPathGuidedTestcaseGenerator.h>

#include <fml/expression/AvmCode.h>

#include <fml/executable/InstanceOfPort.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/trace/TraceFactory.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/SymbexControllerRequestManager.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
AvmPathGuidedTestcaseGenerator::AvmPathGuidedTestcaseGenerator(SymbexControllerUnitManager & aControllerUnitManager,
		const WObject * wfParameterObject)
: RegisteredCoverageProcessorUnit(aControllerUnitManager, wfParameterObject,
		AVM_PREPOST_FILTERING_STAGE | AVM_POST_PROCESSING_STAGE,
		PRECEDENCE_OF_TRANSITION_COVERAGE),
mQuiescenceFactory( *this ),
mTraceDeterministismFactory( *this ),
mTestCaseStatistics( *this, ENV ),
mSolverKind(  SolverDef::SOLVER_UNDEFINED_KIND  ),
mLocalExecutableForm( getConfiguration().getExecutableSystem(), 0 ),
mTraceChecker( ENV, & mLocalExecutableForm ),
mTraceTestPurpose( OperatorManager::OPERATOR_SEQUENCE ),
mTraceCommunicationIO( OperatorManager::OPERATOR_SEQUENCE ),
mUncontrollable( OperatorManager::OPERATOR_INTERLEAVING ),
mUncontrollableTraceFilter( (wfParameterObject != WObject::_NULL_) ?
		wfParameterObject->getNameID() : "AvmTestcaseGenetator" ),
// Computing Local Variables
mTraceOffset( 0 ),
mCurrentTestPurposeEC( ),
mSatTestPurposeEC( ),
mGoalAchieved( false )
{
	//!! NOTHING
}

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmPathGuidedTestcaseGenerator::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();


	const ExecutableSystem & anExecutableSystem =
			getConfiguration().getExecutableSystem();

	mCoverageStatistics.resetCounter();


	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));
	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string solverName =
				Query::getWPropertyString(thePROPERTY, "solver", "");
		if( solverName.empty() )
		{
AVM_IF_DEBUG_FLAG( SOLVING )
	thePROPERTY->warningLocation(AVM_OS_WARN)
			<< "Unexpected an empty solver engine kind!!!!!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( SOLVING )
		}
		mSolverKind = SolverDef::toSolver(
				solverName, SolverDef::DEFAULT_SOLVER_KIND);
	}
	else
	{
		mSolverKind = SolverDef::SOLVER_CVC4_KIND;
	}

	mTraceChecker.setSolverKind( mSolverKind );


	const WObject * theDATA = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("data", "DATA"));
	if( theDATA != WObject::_NULL_ )
	{
		anExecutableSystem.initProcessExecutableForm(
				mLocalExecutableForm, theDATA->ownedSize());

		List< WObject * > listOfLocalVar;
		Query::getListWObject(theDATA, listOfLocalVar);

		TypeSpecifier aTypeSpecifier;

		List< WObject * >::iterator it = listOfLocalVar.begin();
		List< WObject * >::iterator itEnd = listOfLocalVar.end();
		for( avm_offset_t offset = 0 ; it != itEnd ; ++it , ++offset )
		{
			aTypeSpecifier = ENV.getBuilder().getCompiler().
					compileTypeSpecifier(mLocalExecutableForm,
							(*it)->getQualifiedTypeNameID() );

			BF anInstance( new InstanceOfData(
					IPointerVariableNature::POINTER_STANDARD_NATURE,
					&mLocalExecutableForm, Variable::nullref(), aTypeSpecifier,
					(*it)->getFullyQualifiedNameID(), offset) );

			mLocalExecutableForm.setVariable( offset , anInstance );
		}
	}
	else
	{
		anExecutableSystem.initProcessExecutableForm(
				mLocalExecutableForm, 0);
	}


	const WObject * theTRACE = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("trace", "TRACE"));
	if( (theTRACE == WObject::_NULL_) || theTRACE->hasnoOwnedElement() )
	{
		return false;
	}

	// Configuration of TRACE
	TraceFactory traceFactory(getConfiguration(), ENV,
			getParameterWObject(), mLocalExecutableForm);

	if( traceFactory.configure(mTraceTestPurpose) )
	{
		 if( ! traceFactory.collectIO(mTraceTestPurpose, mTraceCommunicationIO) )
		 {
			 return( mConfigFlag = false );
		 }
 AVM_IF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
	AVM_OS_LOG << "Configuration of trace sequence: " << std::endl;
	 mTraceTestPurpose.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	 mTraceCommunicationIO.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
 AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
	}
	else
	{
		 return( mConfigFlag = false );
	}

	const WObject * theUNCONTROLLABLE = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("uncontrollable", "UNCONTROLLABLE"));
	if( (theUNCONTROLLABLE != WObject::_NULL_)
		&& theUNCONTROLLABLE->hasOwnedElement() )
	{
		if( mUncontrollableTraceFilter.configure(ENV,
				getParameterWObject(), "uncontrollable", "UNCONTROLLABLE") )
		{
AVM_IF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
	AVM_OS_LOG << "Configuration of uncontrollable channels: " << std::endl;
	mUncontrollableTraceFilter.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
		}
		else
		{
			 return( mConfigFlag = false );
		}

		TraceFactory traceFactory(getConfiguration(), ENV,
				getParameterWObject(), mLocalExecutableForm);

		if( ! traceFactory.configure(theUNCONTROLLABLE,
				mUncontrollable.getOperands()) )
		{
			 return( mConfigFlag = false );
		}
	}



AVM_IF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )
	AVM_OS_LOG << "The parsed test purpose :> " << std::endl;
	mTraceTestPurpose.toStream( AVM_OS_LOG << AVM_TAB1_INDENT );

	mLocalExecutableForm.toStream( AVM_OS_LOG);
	AVM_OS_LOG << END_INDENT << std::endl;


	AVM_OS_LOG << "The extract IO trace :> " << std::endl;
	mTraceCommunicationIO.toStream( AVM_OS_LOG << AVM_TAB1_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , CONFIGURING )


	mCoverageStatistics.mNumberOfElements = mTraceTestPurpose.size();

	mCoverageStatistics.mCoverageBitset.resize(
			mCoverageStatistics.mNumberOfElements, false);


	mConfigFlag = ( mCoverageStatistics.mNumberOfElements > 0 );

	if( mConfigFlag )
	{
		getConfiguration().setNewfreshParameterExperimentalHeightBasedUID(true);

		mConfigFlag = getExecutionQueue().reconfigure(ExecutionQueue::STRATEGY_ALL);
	}
	return( mConfigFlag );
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmPathGuidedTestcaseGenerator::reportMinimum(OutStream & os) const
{
	os << TAB << "FAM< " << QNID() << " , HoJ > " << this->getNameID() << " "
			<< mCoverageStatistics.strCoverageRate(mGoalAchieved) << " ==> "
			<< (mGoalAchieved ? "DONE !" : "FAILED !")
			<< std::endl;

	mTestCaseStatistics.reportDefault(os);
}


void AvmPathGuidedTestcaseGenerator::reportDefault(OutStream & os) const
{
	os << TAB << "FAM< " << QNID() << " , HoJ > " << this->getNameID() << " "
			<< mCoverageStatistics.strCoverageRate(mGoalAchieved) << " ==> "
			<< (mGoalAchieved ? "DONE !" : "FAILED !")
			<< std::endl;

	mTestCaseStatistics.reportDefault(os);
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void AvmPathGuidedTestcaseGenerator::tddRegressionReportImpl(OutStream & os) const
{
	os << TAB << "CONTROLLED WIDTH EVALUATION : "
			<< mCoverageStatistics.strCoverageRate() << " ==> "
			<< (mGoalAchieved ? "DONE !" : "FAILED !")
			<< EOL_FLUSH;
}

////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

//bool AvmPathGuidedTestcaseGenerator::preprocess()
//{
//	return( true );
//}
//
//
//bool AvmPathGuidedTestcaseGenerator::postprocess()
//{
//	//BaseCoverageFilter::postprocess();
//
//	return( true );
//}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmPathGuidedTestcaseGenerator::filteringInitialize()
{
	// Preserve every root context
	mListOfPositiveEC.append( getExecutionQueue().getInitQueue() );

	return( true );
}


bool AvmPathGuidedTestcaseGenerator::prefilter()
{
	ecQueue = &( getExecutionQueue().getReadyQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; )
	{
		if( not prefilter(* (*ecQueueIt)) )
		{
			getExecutionQueue().appendFailed( *ecQueueIt );

			ecQueueIt = ecQueue->erase(ecQueueIt);
		}
		else
		{
			++ecQueueIt;
		}
	}

	return( BaseCoverageFilter::prefilter() );
}


bool AvmPathGuidedTestcaseGenerator::prefilter(ExecutionContext & anEC)
{
	if( mGoalAchieved )
	{
		getSymbexRequestManager().postRequestStop( this );
	}
	if( ((mTraceOffset == 0) && anEC.getFlags().noneExecutionTrace())
		|| anEC.getFlags().hasCoverageElementTrace() )
	{
		return true;
	}

	return false;
}


bool AvmPathGuidedTestcaseGenerator::filteringFinalize()
{
	return( BaseCoverageFilter::filteringFinalize() );
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmPathGuidedTestcaseGenerator::postfilter()
{
	if( mCoverageStatistics.hasUncovered() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )
		AVM_OS_COUT << "Test purpose :> " << mTraceTestPurpose[mTraceOffset] << std::endl;
		AVM_OS_COUT << "Statement-IO :> " << mTraceCommunicationIO[mTraceOffset] << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( LOW , PROCESSING )

		mSatTestPurposeEC.clear();

		ecQueue = &( getExecutionQueue().getResultQueue() );
		ecQueueItEnd = ecQueue->end();
		for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
		{
			if( postfilter(* (*ecQueueIt)) )
			{
				mSatTestPurposeEC.append(*ecQueueIt);
			}
			else if( mTraceOffset > 0 )
			{
				ecQueueIt = ecQueue->erase(ecQueueIt);
				continue;
			}
			++ecQueueIt;
		}

		if( mSatTestPurposeEC.nonempty() )
		{
			++mTraceOffset;

			mCurrentTestPurposeEC.clear();
			mCurrentTestPurposeEC.append(mSatTestPurposeEC);

			mCoverageStatistics.addCoveredElement();
		}
		else if( mTraceOffset > 0 )
		{
			return false;
		}
	}

	return( getExecutionQueue().hasResult() );
}


bool AvmPathGuidedTestcaseGenerator::postfilter(ExecutionContext & anEC)
{
	bool hasCoveredElement = false;

	for( const auto & aChildEC : anEC.getChildContexts()  )
	{
		if( mTraceChecker.isSat(*aChildEC, mTraceTestPurpose[mTraceOffset]) )
		{
			hasCoveredElement = true;

			aChildEC->addInfo( *this, mTraceTestPurpose[mTraceOffset] );

			aChildEC->getwFlags().setCoverageElementTrace();
			aChildEC->getwFlags().setObjectiveAchievedTrace();
			if( mCoverageStatistics.getNumberOfCovered() == 0 )
			{
				anEC.getwFlags().setCoverageElementTrace();
				anEC.getwFlags().setObjectiveAchievedTrace();
			}
			if( mCoverageStatistics.getNumberOfUncovered() == 1 )
			{
				mGoalAchieved = true;
			}
		}
//@! TO UNCOMMENT with FACS Performance evaluation
		else if( mTraceChecker.isSat(*aChildEC, mTraceCommunicationIO[mTraceOffset]) )
		{
			const BF & ioTrace = aChildEC->getIOElementTrace();
			const BFCode & comTrace = BaseEnvironment::searchTraceIO(ioTrace);
			const InstanceOfPort & comPort = comTrace->first().to< InstanceOfPort >();

			if( not mTraceDeterministismFactory.checkDeterminism(anEC, comPort, *aChildEC) )
			{
				hasCoveredElement = true;

				aChildEC->addInfo( *this, mTraceCommunicationIO[mTraceOffset] );
				aChildEC->getwFlags().setCoverageElementTrace();
			}
		}
	}

	mQuiescenceFactory.quiescenceOf(anEC);

	return( hasCoveredElement );
}


////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmPathGuidedTestcaseGenerator::postprocess()
{
//	// Quiescence generation
//	AvmQuiescenceFactory quiescenceFactory(*this);
//
//	quiescenceFactory.buildGraph();
//
//	AvmTraceDeterminismFactory traceDeterministic(*this);
//	traceDeterministic.checkDeterminism();
//
//	// LabelledTestcase generation
//	AvmLabelledTestCaseFactory labelledTestcaseFactory(*this,
//			mQuiescenceFactory.getQuiescencePort());
//
//	labelledTestcaseFactory.buildTestCase();

	// Testcase generation
	AvmTestCaseFactory testcaseFactory(*this, mTestCaseStatistics,
			mQuiescenceFactory.getQuiescencePort());

	testcaseFactory.buildTestCase();

	return( true );
}

} /* namespace sep */
