/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "RedundancyFilter.h"

#include "ConfigurationComparator.h"

#include "PathScopeIterator.h"

#include "BaseDataComparator.h"
#include "DataSolverComparator.h"
#include "DataSyntaxicEquivalence.h"

#include <fam/api/MainProcessorUnit.h>

#include <fam/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/Workflow.h>


namespace sep
{

/**
 * DESTRUCTOR
 */
RedundancyFilter::~RedundancyFilter()
{
	if( mRedundancyEnabledFlag )
	{
		// Unregistration
		getSymbexEventManager().unregisterHandlerEventDestroyCtx(this);
	}

	destroy();
}


void RedundancyFilter::destroy()
{
	if( mConfigurationComparator != NULL )
	{
		delete mConfigurationComparator;
	}

	if( mPathScopeIterator != NULL )
	{
		delete mPathScopeIterator;
	}

	if( mExecutionDataComparator != NULL )
	{
		delete mExecutionDataComparator;
	}
}


/**
 ***************************************************************************
prototype filter::redundancy as avm::core.filter.REDUNDANCY is
section PROPERTY
	@predicate = 'INCLUSION';  // ( <=  | INC | INCLUSION )
	                              ( ==  | EQ  | EQUALITY )
	                              ( =a= | AEQ | ALPHA_EQUIV)
	                              ( =s= | SEQ | SYNTAXIC_EQUALITY)
	                              ( =t= | TEQ | TRIVIALLY_EQUALITY)
	                              NONE

	@solver = 'OMEGA';         // OMEGA | CVC4

	@path_scope = 'ALL';       // ALL execution graph path
	                              CURRENT execution graph path
	                              PARENT execution graph node

	@data_scope = 'ALL';       // ALL data ; or DETAILS section
	                           // DETAILS | DETAILS< exclude > some data,
endsection PROPERTY

section HEURISTIC
	@communication = false;

	@variable = true;
	@path_condition = false;
endsection HEURISTIC

section DETAILS
	@model = ufi;

	@instance = ufi;

	@variable = ufi;
endsection DETAILS
endprototype
***************************************************************************
*/

/*
 * NEW CONSISE SYNTAX
supervisor {
	limit 'of graph exploration' [
		eval = 10
		...
	]
	queue 'for graph exploration' [
		strategy = 'BFS'
		...
	]
	redundancy 'detection strategy' [
		comparer = 'INCLUSION'
		solver = 'OMEGA'
		path_scope = 'CURRENT'
		data_scope = 'ALL'
	] // end redundancy

	console [
		format = "\nstep:%1% , context:%2% , height:%3% , width:%4%"
		...
	]
}
*/


bool RedundancyFilter::configureImpl()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
			<< "Unexpected a <null> RedundancyFilter WObject !!!"
			<< SEND_EXIT;

	mConfigFlag = true;

	mRedundancyConfigurationFlag = false;

	bool isnotDefinedWTypedObjectParameters = false;

	WObject * wfRedundancy = mParameterWObject;

	if( MainProcessorUnit::AUTO_REGISTER_TOOL.isTypeID( *mParameterWObject ) )
	{
		wfRedundancy = Query::getRegexWObjectByNameID(mParameterWObject,
				PREFIX_WID("symbex", OR_WID2("redundancy", "REDUNDANCY")),
				WObject::_NULL_);

		if( wfRedundancy == WObject::_NULL_ )
		{
			mRedundancyEnabledFlag = false;

			// Trivial Loop Detection Enabling
			mTrivialLoopDetectionFlag =
					Query::getRegexWPropertyBoolean(mParameterWObject,
					CONS_WID3("loop", "detection", "trivial"), true);

			return( mConfigFlag = true );
		}
		else if( wfRedundancy->isWTypedOrReference() )
		{
			if( wfRedundancy->isWPropertyWReference() )
			{
				wfRedundancy = wfRedundancy->getWReferenceValue();
			}

			if( RedundancyFilter::AUTO_REGISTER_TOOL.isTypeID( *wfRedundancy ) )
			{
				mParameterWObject = wfRedundancy;
			}
			else
			{
				AVM_OS_WARN << "RedundancyFilter::configure:> "
						"Unexpected the WObject< "
						<< wfRedundancy->getFullyQualifiedNameID()
						<< " > as redundancy parameters defined in supervisor <"
						<< mParameterWObject->getFullyQualifiedNameID()
						<< " >! " << std::endl;

				mRedundancyEnabledFlag = mConfigFlag = false;

				return( mConfigFlag );
			}
		}
		else if( wfRedundancy->isWSequence() )
		{
			isnotDefinedWTypedObjectParameters = true;
		}
		else if( not wfRedundancy->isWSequence() )
		{
			AVM_OS_WARN << "RedundancyFilter::configure:> "
					"Unexpected the WObject< " << wfRedundancy->strHeader()
					<< " > as redundancy parameters defined in supervisor <"
					<< mParameterWObject->getFullyQualifiedNameID()
					<< " >! " << std::endl;

			mRedundancyEnabledFlag = mConfigFlag = false;

			return( mConfigFlag );
		}
	}

	WObject * thePROPERTY = (isnotDefinedWTypedObjectParameters) ? wfRedundancy
			: Query::getRegexWSequence(wfRedundancy, OR_WID4("property",
					"PROPERTY", "redundancy", "REDUNDANCY"), wfRedundancy);


	// Trivial Loop Detection Enabling
	mTrivialLoopDetectionFlag =
			Query::getRegexWPropertyBoolean(thePROPERTY,
				CONS_WID3("loop", "detection", "trivial"), true);

	if( (thePROPERTY == WObject::_NULL_)
		|| (thePROPERTY->isWTypedOrSequence()
			&& thePROPERTY->hasnoOwnedElement()) )
	{
		return( mConfigFlag );
	}

	////////////////////////////////////////////////////////////////////////////
	// PREDICATE KIND
	////////////////////////////////////////////////////////////////////////////
	std::string strPredicate = Query::getRegexWPropertyString(
			thePROPERTY, OR_WID2("comparer", "predicate"), "");

	if( strPredicate.empty() )
	{
		return( mConfigFlag );
	}

	else if( (strPredicate == "<=")
			|| (strPredicate == "INC")
			|| (strPredicate == "INCLUSION") )
	{
		mExecutionDataComparator =
				new DataSolverInclusion( getConfiguration() );
	}
	else if( (strPredicate == "==")
			|| (strPredicate == "EQ")
			|| (strPredicate == "EQUALITY") )
	{
		mExecutionDataComparator =
				new DataSolverEquality( getConfiguration() );
	}
	else if( (strPredicate == "=a=")
			|| (strPredicate == "AEQ")
			|| (strPredicate == "ALPHA_EQUIV") )
	{
		mExecutionDataComparator =
				new DataAlphaEquivalence( getConfiguration() );
	}
	else if( (strPredicate == "=s=")
			|| (strPredicate == "SEQ")
			|| (strPredicate == "SYNTAXIC_EQUALITY") )
	{
		mExecutionDataComparator =
				new DataSyntaxicEquivalence( getConfiguration() );
	}
	else if( (strPredicate == "=&=")
			|| (strPredicate == "=t=")
			|| (strPredicate == "TEQ")
			|| (strPredicate == "TRIVIALLY_EQUALITY") )
	{
		mExecutionDataComparator =
				new TriviallyDataComparison( getConfiguration() );
		strPredicate = "=t=";
	}
	else if( strPredicate == "NONE" )
	{
		mExecutionDataComparator = new NoneDataComparison( getConfiguration() );
	}
	else
	{
		AVM_OS_ERROR_ALERT << "Unexpected REDUNDANCY filter << @predicate = "
				<< strPredicate << "; >> !!!" << std::endl
				<< "NB. << @predicate = { 'INCLUSION' | 'EQUALITY' | "
				"'ALPHA_EQUIV' | 'SYNTAXIC_EQUALITY' | 'TRIVIALLY_EQUALITY' | "
				"'NONE' }; >> !!!"
				<< SEND_ALERT;

		mConfigFlag = false;
	}


	////////////////////////////////////////////////////////////////////////////
	// DATA SCOPE
	////////////////////////////////////////////////////////////////////////////
	if( mExecutionDataComparator != NULL )
	{
		if( mExecutionDataComparator->configure( mParameterWObject ) )
		{
			if( (not mExecutionDataComparator->hasVariableComparison())
				&& (strPredicate != "=t=")
				&& (strPredicate != "NONE") )
			{
				delete mExecutionDataComparator;

				mExecutionDataComparator =
						new NoneDataComparison( getConfiguration() );
			}
		}
		else
		{
			destroy();

			mConfigFlag = false;
		}
	}


	////////////////////////////////////////////////////////////////////////////
	// STATE SCOPE
	////////////////////////////////////////////////////////////////////////////
	std::string control_scope = Query::getRegexWPropertyString(
			thePROPERTY, CONS_WID2("control", "scope"), "ALL");
	if( control_scope == "ALL" )
	{
		mConfigurationComparator =
				new BaseConfigurationComparator( getConfiguration() );
	}
	else if( control_scope == "DETAILS" )
	{
		mConfigurationComparator =
				new DetailConfigurationComparator( getConfiguration() );
	}
	else
	{
		AVM_OS_ERROR_ALERT
				<< "Unexpected REDUNDANCY filter << @control_scope = "
				<< control_scope << "; >> !!!" << std::endl
				<< "NB. << @control_scope = { 'ALL' | 'DETAILS' }; >> !!!"
				<< SEND_ALERT;

		mConfigFlag = false;
	}

	mConfigFlag = mConfigurationComparator->configure( mParameterWObject )
				&& mConfigFlag;


	////////////////////////////////////////////////////////////////////////////
	// PATH SCOPE
	////////////////////////////////////////////////////////////////////////////
	std::string path_scope = Query::getRegexWPropertyString(
			thePROPERTY, CONS_WID2("path", "scope"), "ALL");
	if( path_scope == "ALL" )
	{
		mPathScopeIterator =
				new AllPathScopeIterator(mConfigurationComparator);
	}
	else if( path_scope == "CURRENT" )
	{
		mPathScopeIterator =
				new CurrentPathScopeIterator(mConfigurationComparator);
	}
	else if( path_scope == "PARENT" )
	{
		mPathScopeIterator =
				new ParentPathScopeIterator(mConfigurationComparator);
	}
	else
	{
		AVM_OS_ERROR_ALERT << "Unexpected REDUNDANCY filter << @path_scope = "
				<< path_scope << "; >> !!!" << std::endl
				<< "NB. << @path_scope = { 'ALL' | 'CURRENT' | PARENT }; >> !!!"
				<< SEND_ALERT;

		mConfigFlag = false;
	}

	if( mConfigFlag )
	{
		mConfigFlag = mPathScopeIterator->configure( mParameterWObject );

		if( mConfigFlag )
		{
			// Registration to handler DestroyCtx event
			getSymbexEventManager().registerHandlerEventDestroyCtx(this);
		}
	}

	mRedundancyConfigurationFlag = mRedundancyEnabledFlag = mConfigFlag;

	return( mConfigFlag );
}


/**
 * preFilter
 * Every pre filter has to implement this method
 */
bool RedundancyFilter::prefilter()
{
	ecQueue = &( getExecutionQueue().getReadyQueue() );
	ecQueueItEnd = ecQueue->end();
	for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
	{
		if( not prefilter( * (*ecQueueIt)) )
		{
			getExecutionQueue().appendFailed( *ecQueueIt );

			ecQueueIt = ecQueue->erase(ecQueueIt);
		}
		else
		{
			++ecQueueIt;
		}
	}

	return( getExecutionQueue().hasReady() );
}


bool RedundancyFilter::prefilter(ExecutionContext & anEC)
{
	if( trivialLoopDetection(anEC) )
	{
		return( false );
	}

	else if( mRedundancyEnabledFlag )
	{
		mPathScopeIterator->begin(& anEC);
		for( ; mPathScopeIterator->hasNext() ; mPathScopeIterator->next() )
		{
			++mRedundancyTest;

			mCandidateEC = mPathScopeIterator->current();

			if( getExecutionDataComparator()->compare(
					anEC, (* mCandidateEC)) )
			{
				++mRedundancyCount;

				anEC.getwFlags().setExecutionRedundancyTrace();

				anEC.addInfo(*this, mCandidateEC->getHeader());

				const_cast< ExecutionContext * >( mCandidateEC )->
						getwFlags().setExecutionRedundancyTargetTrace();

				// DO DIAGNOSTIQ
AVM_IF_DEBUG_LEVEL_OR_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << std::endl << DEFAULT_WRAP_DATA << "REDUNDANT EC :> ";
	anEC.traceDefault(AVM_OS_TRACE);

	AVM_OS_TRACE << "FOUND[" << std::setw(5)
			<< mRedundancyCount << "] :> ";
	mCandidateEC->traceDefault(AVM_OS_TRACE);
	AVM_OS_TRACE << END_WRAP_EOL;


	AVM_OS_COUT << std::endl << DEFAULT_WRAP_DATA << "REDUNDANT EC :> ";
	anEC.traceDefault(AVM_OS_COUT);

	AVM_OS_COUT << "FOUND[" << std::setw(5)
			<< mRedundancyCount << "] :> ";
	mCandidateEC->traceDefault(AVM_OS_COUT);
	AVM_OS_COUT << END_WRAP_EOL;
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG( MEDIUM , REDUNDANCE )

				return( false );
			}
			else
			{
			// DO DIAGNOSTIQ
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << DEFAULT_WRAP_DATA << "NEW EC :> ";
	anEC.traceDefault(AVM_OS_TRACE);

	AVM_OS_TRACE << "OLD EC :> ";
	mCandidateEC->traceDefault(AVM_OS_TRACE);
	AVM_OS_TRACE << END_WRAP_EOL;


	AVM_OS_COUT << DEFAULT_WRAP_DATA << "NEW EC :> ";
	anEC.traceDefault(AVM_OS_COUT);

	AVM_OS_COUT << "OLD EC :> ";
	mCandidateEC->traceDefault(AVM_OS_COUT);
	AVM_OS_COUT << END_WRAP_EOL;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , REDUNDANCE )
			}
		}

		mPathScopeIterator->hash( anEC );

AVM_IF_DEBUG_ENABLED
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_ENABLED
	}

	return( true );
}


bool RedundancyFilter::trivialLoopDetection(ExecutionContext & anEC)
{
	ExecutionContext * prevEC = anEC.getPrevious();
	bool foondLoop = false;

	if( mTrivialLoopDetectionFlag )
	{
		for( ; (prevEC != NULL) && prevEC->isnotRoot() ;
				prevEC = prevEC->getPrevious()  )
		{
			if( anEC.refExecutionData().isTEQ( prevEC->getExecutionData() ) )
			{
				++mTrivialLoopCount;

				foondLoop = true;

				break;
			}
		}
	}
	else if( (prevEC != NULL) && prevEC->isnotRoot()
			&& anEC.refExecutionData().isTEQ( prevEC->getExecutionData() ) )
	{
		++mTrivialLoopCount;

		foondLoop = true;
	}

	if( foondLoop )
	{
		anEC.getwFlags().setExecutionTrivialLoopTrace();

		// DO DIAGNOSTIQ
AVM_IF_DEBUG_LEVEL_OR_FLAG( MEDIUM , REDUNDANCE )
	AVM_OS_TRACE << std::endl << "TRIVIAL LOOP DETECTION :> ";
	anEC.traceDefault(AVM_OS_TRACE);

	AVM_OS_TRACE << "FOUND[" << std::setw(5)
			<< mTrivialLoopCount << "] :> ";
	prevEC->traceDefault(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;


	AVM_OS_COUT << std::endl << "TRIVIAL LOOP :> ";
	anEC.traceDefault(AVM_OS_COUT);

	AVM_OS_COUT << "COUNT[" << std::setw(5)
			<< mTrivialLoopCount << "] :> ";
	prevEC->traceDefault(AVM_OS_COUT);
	AVM_OS_COUT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_OR_FLAG( MEDIUM , REDUNDANCE )

		return( true );
	}

	return( false );
}


/**
 * IHandlerEventDestroyCtx API
 * Destroy Execution Context
 */
void RedundancyFilter::handleEventDestroyCtx(ExecutionContext * anEC)
{
	mPathScopeIterator->handleEventDestroyCtx(anEC);
}

/**
 * REPORT TRACE
 */
void RedundancyFilter::reportDefault(OutStream & os) const
{
	if( (mRedundancyTest > 0) || (mTrivialLoopTest > 0) )
	{
		reportHeader(os, "REDUNDANCY");

		if( mRedundancyEnabledFlag && (mRedundancyTest > 0) )
		{
			os << TAB2 << "Comparer predicate: "
					<< mExecutionDataComparator->strComparer() << EOL
					<< TAB2 << "The redundancy count: " << mRedundancyCount
					<< " for " << mRedundancyTest << " tests !" << EOL_FLUSH;
		}

		if( mTrivialLoopDetectionFlag && (mTrivialLoopTest > 0) )
		{
			os << TAB2 << "The trivial loop count: " << mTrivialLoopCount
					<< " for " << mTrivialLoopTest << " tests !" << EOL_FLUSH;
		}
	}
}

////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void RedundancyFilter::tddRegressionReportImpl(OutStream & os)
{
	os << TAB << "REDUNDANCY - positive detection count : "
			<< mRedundancyCount
			<< " for " << mRedundancyTest << " tests" << EOL_FLUSH;
}


}
