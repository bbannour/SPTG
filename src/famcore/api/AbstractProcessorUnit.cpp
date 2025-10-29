/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 28 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AbstractProcessorUnit.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/ExecutableSystem.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include  <famcore/queue/WaitingStrategy.h>
#include <sew/SymbexControllerEventManager.h>

#include <sew/SymbexDispatcher.h>
#include <sew/SymbexEngine.h>
#include <boost/format.hpp>



namespace sep
{

/*
 * Precedence for processor, based on resource consumption,
 * used to order processor in the Diversity process !
 * For info: 0 for minimum resource requirement reserved by the main processor,
 * the STOP CRITERIA, and a great number for example REDUNDANCY processor !
 * {
 *   preProcessing , postProcessing ,
 *   filteringInitialize , filteringFinalize
 *   preFiltering , postFiltering
 * }
 */
const std::uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_PROCESSOR[5] =
		{ 50 , 50 , 50 , 50 , 50 };

const std::uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_MAIN_PROCESSOR[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_ACTIVE_COVERAGE_PROCESSOR[5] =
		{ 40 , 40 , 40 , 40 , 40 };

const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_PASSIVE_COVERAGE_PROCESSOR[5] =
		{ 60 , 60 , 60 , 60 , 60 };


const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_MAIN_PROCESSOR[5] =
		{ 0 , 0 , 0 , 0 , 0 };

const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_EXTENDER_PROCESSOR[5] =
		{ 10 , 10 , 10 , 10 , 10 };

const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_REDUNDANCY[5] =
		{ 100 , 100 , 100 , 100 , 100 };


const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_TRANSITION_COVERAGE[5] =
		{ 40 , 40 , 40 , 40 , 40 };

const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_HIT_OR_JUMP[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_FORMULA_COVERAGE[5] =
		{ 60 , 60 , 60 , 60 , 60 };

const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_MACHINE_COVERAGE[5] =
		{ 60 , 60 , 60 , 60 , 60 };


const std::uint8_t AbstractProcessorUnit::PRECEDENCE_OF_TEST_OFFLINE[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const std::uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR[5] =
		{ 75 , 75 , 75 , 75 , 75 };


/**
 * CONSTRUCTOR
 * Default
 */
AbstractProcessorUnit::AbstractProcessorUnit(
		SymbexControllerUnitManager & aManager,
		const WObject * wfParameterObject,
		avm_computing_process_stage_t requiredStage,
		const std::uint8_t * aPrecedence)
: RunnableElement( CLASS_KIND_T( AbstractProcessorUnit ) , wfParameterObject ),
IProcessorUnitTest( *this ),
mControllerUnitManager( aManager ),
ENV( aManager.getPrimitiveProcessor() ),

mComputingStageRequired( requiredStage ),
mComputingStageEnabled( AVM_UNDEFINED_STAGE ),

mAutoConfigure( false ),
mAutoStart( false ),

mPrecedenceOfPreProcess( aPrecedence[0] ),
mPrecedenceOfPostProcess( aPrecedence[1] ),

mPrecedenceOfInitFilter( aPrecedence[2] ),

mPrecedenceOfPreFilter( aPrecedence[3] ),
mPrecedenceOfPostFilter( aPrecedence[4] ),

mBeginningStepTimout( 0 ),

mStopFlag( false ),
mBreakFlag( false ),

mSliceFlag( false ),
mSliceCount( 0 ),

mSpiderInitTraceFormatter( ),
mSpiderStepTraceFormatter( ),
mSpiderStopTraceFormatter( ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( nullptr ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}


AbstractProcessorUnit::AbstractProcessorUnit(SymbexControllerUnitManager & aManager,
		const WObject * wfParameterObject, const std::uint8_t * aPrecedence)
: RunnableElement( CLASS_KIND_T( AbstractProcessorUnit ) , wfParameterObject ),
IProcessorUnitTest( *this ),
mControllerUnitManager( aManager ),
ENV( aManager.getPrimitiveProcessor() ),

mComputingStageRequired( AVM_UNDEFINED_STAGE ),
mComputingStageEnabled( AVM_UNDEFINED_STAGE ),

mAutoConfigure( false ),
mAutoStart( false ),

mPrecedenceOfPreProcess( aPrecedence[0] ),
mPrecedenceOfPostProcess( aPrecedence[1] ),

mPrecedenceOfInitFilter( aPrecedence[2] ),

mPrecedenceOfPreFilter( aPrecedence[3] ),
mPrecedenceOfPostFilter( aPrecedence[4] ),

mBeginningStepTimout( 0 ),

mStopFlag( false ),
mBreakFlag( false ),

mSliceFlag( false ),
mSliceCount( 0 ),

mSpiderInitTraceFormatter( ),
mSpiderStepTraceFormatter( ),
mSpiderStopTraceFormatter( ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( nullptr ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}



/**
 * CONSTRUCTOR
 * Other
 */
AbstractProcessorUnit::AbstractProcessorUnit(class_kind_t aClassKind,
	SymbexControllerUnitManager & aManager, const WObject * wfParameterObject)
: RunnableElement( aClassKind , wfParameterObject ),
IProcessorUnitTest( *this ),
mControllerUnitManager( aManager ),
ENV( aManager.getPrimitiveProcessor() ),

mComputingStageRequired( AVM_UNDEFINED_STAGE ),
mComputingStageEnabled( AVM_UNDEFINED_STAGE ),

mAutoConfigure( false ),
mAutoStart( false ),

mPrecedenceOfPreProcess( 0 ),
mPrecedenceOfPostProcess( 0 ),

mPrecedenceOfInitFilter( 0 ),

mPrecedenceOfPreFilter( 0 ),
mPrecedenceOfPostFilter( 0 ),

mBeginningStepTimout( 0 ),

mStopFlag( false ),
mBreakFlag( false ),

mSliceFlag( false ),
mSliceCount( 0 ),

mSpiderInitTraceFormatter( ),
mSpiderStepTraceFormatter( ),
mSpiderStopTraceFormatter( ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( nullptr ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}

AbstractProcessorUnit::AbstractProcessorUnit(class_kind_t aClassKind,
		SymbexEngine & anEngine, SymbexControllerUnitManager & aManager,
		const WObject * wfParameterObject)
: RunnableElement( aClassKind, wfParameterObject ),
IProcessorUnitTest( *this ),
mControllerUnitManager( aManager ),
ENV( anEngine.getPrimitiveProcessor() ),

mComputingStageRequired( AVM_UNDEFINED_STAGE ),
mComputingStageEnabled( AVM_UNDEFINED_STAGE ),

mAutoConfigure( false ),
mAutoStart( false ),

mPrecedenceOfPreProcess( 0 ),
mPrecedenceOfPostProcess( 0 ),

mPrecedenceOfInitFilter( 0 ),

mPrecedenceOfPreFilter( 0 ),
mPrecedenceOfPostFilter( 0 ),

mBeginningStepTimout( 0 ),

mStopFlag( false ),
mBreakFlag( false ),

mSliceFlag( false ),
mSliceCount( 0 ),

mSpiderInitTraceFormatter( ),
mSpiderStepTraceFormatter( ),
mSpiderStopTraceFormatter( ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( nullptr ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}


/**
 * GETTER
 * SymbexEngine
 * Configuration
 * SymbexDispatcher
 *
 */
SymbexEngine & AbstractProcessorUnit::getSymbexEngine() const
{
	return( mControllerUnitManager.getSymbexEngine() );
}

Configuration & AbstractProcessorUnit::getConfiguration() const
{
	return( mControllerUnitManager.getSymbexEngine().getConfiguration() );
}

SymbexDispatcher & AbstractProcessorUnit::getSymbexDispatcher() const
{
	return( mControllerUnitManager.getSymbexEngine().getSymbexDispatcher() );
}

SymbexControllerEventManager & AbstractProcessorUnit::getSymbexEventManager() const
{
	return( getSymbexDispatcher().getSymbexEventManager() );
}

SymbexControllerRequestManager &
AbstractProcessorUnit::getSymbexRequestManager() const
{
	return( getSymbexDispatcher().getSymbexControllerRequestManager() );
}

/**
 * new local ExecutableForm for Processor usage
 */
//!@?UNUSED: TO DELETE
ExecutableForm * AbstractProcessorUnit::newLocalExecutableForm()
{
	ExecutableForm * localExec = new ExecutableForm(
			getConfiguration().getExecutableSystem() , 0 );

	if( hasParameterWObject() )
	{
		localExec->updateFullyQualifiedNameID(
				getParameterWObject()->getFullyQualifiedNameID() );
	}

	return( localExec );
}

///**
// * GETTER
// * mProcessorManager
// */
//MainProcessorUnit & AbstractProcessorUnit::getMainProcessor()
//{
//	return( mProcessorManager.getMainProcessor() );
//}
//
//const MainProcessorUnit & AbstractProcessorUnit::getMainProcessor() const
//{
//	return( mProcessorManager.getMainProcessor() );
//}
//
//
///**
// * GETTER
// * the Builder
// */
//Builder & AbstractProcessorUnit::getBuilder()
//{
//	return( mProcessorManager.getBuilder() );
//}
//
//
///**
// * GETTER
// * AvmPrimitiveProcessor
// */
//AvmPrimitiveProcessor & AbstractProcessorUnit::getPrimitiveProcessor()
//{
//	return( mProcessorManager.getPrimitiveProcessor() );
//}

/**
 * GETTER
 * theExecutionQueue
 */
ExecutionQueue & AbstractProcessorUnit::getExecutionQueue()
{
	return( mControllerUnitManager.getExecutionQueue() );
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AbstractProcessorUnit::preConfigure()
{
	const WObject * theCONFIG = getParameterWObject();

	theCONFIG = Query::getRegexWSequence(theCONFIG,
				OR_WID2("manifest", "MANIFEST"), theCONFIG);

	if( theCONFIG != WObject::_NULL_ )
	{
		mAutoStart = mControllerUnitManager.isAutoStart()
				|| Query::getRegexWPropertyBoolean(theCONFIG,
						CONS_WID2("auto", "start"), false);

		mAutoConfigure = mAutoStart
				|| mControllerUnitManager.isAutoConfigure()
				|| Query::getRegexWPropertyBoolean(theCONFIG,
						CONS_WID2("auto", "conf(igure)?"), false);
	}

	return( mAutoConfigure || mAutoStart || isEnablePlugin() );
}

bool AbstractProcessorUnit::configure()
{
	// INITIALIZATION
	mConfigFlag = RunnableElement::configure();

	// For common parameters configuration
	mConfigFlag = configureCommon() && mConfigFlag;

	// standard processor user configuration
	mConfigFlag = configureImpl() && mConfigFlag;

	// auto registration
	mConfigFlag = autoConfigureMOE() && mConfigFlag;

	// scheduling configuration
	mConfigFlag = configureLifecycleState() && mConfigFlag;

	return( mConfigFlag );
}


bool AbstractProcessorUnit::configureCommon()
{
	bool isOK = true;

	const WObject * thePROPERTY = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mStopFlag  = Query::getWPropertyBoolean(thePROPERTY, "stop", false);

		mBreakFlag = Query::getWPropertyBoolean(thePROPERTY, "break", false);

		mSliceFlag = Query::getWPropertyBoolean(thePROPERTY, "slice", false);
	}

	// For Eval Trace format
	isOK = configureLog() && isOK;

	return( isOK );
}


bool AbstractProcessorUnit::configureLog()
{
	bool isOK = true;

	mSpiderInitTraceFormatter = getDefaultSpiderInitTraceFormatter();

	mSpiderStepTraceFormatter = getDefaultSpiderStepTraceFormatter();

	mSpiderStopTraceFormatter = getDefaultSpiderStopTraceFormatter();


	mPreEvalTraceFormatter = getDefaultPreEvalTraceFormatter();

	mPostEvalTraceFormatter = getDefaultPostEvalTraceFormatter();

	mBoundEvalTraceFormatter = getDefaultBoundEvalTraceFormatter();

	mReportEvalTraceFormatter = getDefaultReportEvalTraceFormatter();

	const WObject * theLOG = Query::getWSequenceOrElse(
			getParameterWObject(), "console", "LOG");
	if( theLOG != WObject::_NULL_ )
	{
		mSpiderInitTraceFormatter = Query::getRegexWPropertyString(
				theLOG, CONS_WID2("spider" , "init"), mSpiderInitTraceFormatter );

		StringTools::replaceAllEscapeSequences(mSpiderInitTraceFormatter);

		mSpiderStepTraceFormatter = Query::getRegexWPropertyString(
				theLOG, CONS_WID2("spider" , "step"), mSpiderStepTraceFormatter );

		StringTools::replaceAllEscapeSequences(mSpiderStepTraceFormatter);

		mSpiderStopTraceFormatter = Query::getRegexWPropertyString(
				theLOG, CONS_WID2("spider" , "stop"), mSpiderStopTraceFormatter );

		StringTools::replaceAllEscapeSequences(mSpiderStopTraceFormatter);


		std::string defaultFormat = Query::getWPropertyString(
				theLOG, "format", mPreEvalTraceFormatter);

		mPreEvalTraceFormatter = Query::getWPropertyStringOrElse(
				theLOG, "step", "eval", defaultFormat );

		StringTools::replaceAllEscapeSequences(mPreEvalTraceFormatter);


		mPostEvalTraceFormatter = Query::getWPropertyStringOrElse(
				theLOG, "result", "format", mPostEvalTraceFormatter );

		StringTools::replaceAllEscapeSequences(mPostEvalTraceFormatter);


		mBoundEvalTraceFormatter = Query::getWPropertyStringOrElse(
				theLOG, "bound", "format", mBoundEvalTraceFormatter );

		StringTools::replaceAllEscapeSequences(mBoundEvalTraceFormatter);


		mReportEvalTraceFormatter = Query::getWPropertyStringOrElse(
				theLOG, "report", "format", mReportEvalTraceFormatter );

		StringTools::replaceAllEscapeSequences(mReportEvalTraceFormatter);
	}

	if( theLOG == nullptr )
	{
		theLOG = getParameterWObject();
	}

	try
	{
		boost::format formatter(mPreEvalTraceFormatter);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute( theLOG, "eval", bfs.what());
		isOK = false;
	}

	try
	{
		boost::format formatter(mPreEvalTraceFormatter);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute( theLOG, "result", bfs.what());
		isOK = false;
	}

	try
	{
		boost::format formatter(mBoundEvalTraceFormatter);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute( theLOG, "bound", bfs.what());
		isOK = false;
	}

	try
	{
		boost::format formatter(mReportEvalTraceFormatter);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute( theLOG, "report", bfs.what());
		isOK = false;
	}

	return( isOK );
}


bool AbstractProcessorUnit::checkingConfiguration()
{
	if( requiresStrongEnableFilter() && (not isStrongEnableFilter()) )
	{
		AVM_OS_CLOG << strTypeId()
				<< ":> Failed to configure the CONTROLLER UNIT << "
				<< strUniqId() << " >> " << std::endl;

		if( isEnablePrefilter() )
		{
			AVM_OS_CLOG << "This CONTROLLER UNIT must be "
					"in the POST-FILTER scheduler also !"
					<< std::endl;
		}
		else
		{
			AVM_OS_CLOG << "This CONTROLLER UNIT must be "
					"in the PRE-FILTER scheduler also !"
					<< std::endl;
		}

		return( false );
	}

	return true;
}


/**
 * API
 * Auto configure Model Of Execution in CPU
 */
bool AbstractProcessorUnit::autoConfigureMOE()
{
	bool isOK = true;

	if( mAutoConfigure )
	{
		isOK = autoConfigureMOEImpl();
	}

	// checking of model of execution for processor
	isOK = checkingConfiguration() && isOK;

	return( isOK );
}

bool AbstractProcessorUnit::autoConfigureMOEImpl()
{
	bool isOK = true;

	if( mComputingStageRequired != AVM_UNDEFINED_STAGE )
	{
		// We need to deal with the configureImpl() requirement
		// like enablePreprocess( this );
		// using |=
		mComputingStageEnabled |= mComputingStageRequired;

		if( (mComputingStageRequired & AVM_PRE_PROCESSING_STAGE) != 0 )
		{
			if( not mControllerUnitManager.registerPreprocessor( this ) )
			{
				isOK = false;
			}
		}

		if( (mComputingStageRequired & AVM_POST_PROCESSING_STAGE) != 0 )
		{
			if( not mControllerUnitManager.registerPostprocessor( this ) )
			{
				isOK = false;
			}
		}

		if( (mComputingStageRequired & AVM_PRE_FILTERING_STAGE) != 0 )
		{
			if( not mControllerUnitManager.registerPrefilter( this ) )
			{
				isOK = false;
			}
		}

		if( (mComputingStageRequired & AVM_POST_FILTERING_STAGE) != 0 )
		{
			if( not mControllerUnitManager.registerPostfilter( this ) )
			{
				isOK = false;
			}
		}
	}
	else
	{
AVM_OS_DEBUG << "TODO autoConfigureMOEImpl< " << this->strUniqId() << " >" << std::endl;
	}

	return( isOK );
}


////////////////////////////////////////////////////////////////////////////////
// ENABLE & REGISTER  PROCESS PLUGIN
////////////////////////////////////////////////////////////////////////////////

void AbstractProcessorUnit::enablePreprocess(AbstractProcessorUnit * aProcessor)
{
	enablePreprocess();

	mControllerUnitManager.addPreprocessor( aProcessor );
}

void AbstractProcessorUnit::enablePostprocess(AbstractProcessorUnit * aProcessor)
{
	enablePostprocess();

	mControllerUnitManager.addPostprocessor( aProcessor );
}


void AbstractProcessorUnit::enablePrefilter(AbstractProcessorUnit * aProcessor)
{
	enablePrefilter();

	mControllerUnitManager.addPrefilter( aProcessor );
}

void AbstractProcessorUnit::enablePostfilter(AbstractProcessorUnit * aProcessor)
{
	enablePostfilter();

	mControllerUnitManager.addPostfilter( aProcessor );
}



////////////////////////////////////////////////////////////////////////////////
// FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AbstractProcessorUnit::prefilter()
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

	return( getExecutionQueue().hasReady() );
}


bool AbstractProcessorUnit::postfilter()
{
	ecQueue = &( getExecutionQueue().getResultQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; )
	{
		if( mBeginningStepTimout > 0 )
		{
			++ecQueueIt;

			--mBeginningStepTimout;
		}
		else
		{
			if( not postfilter(* (*ecQueueIt)) )
			{
				getExecutionQueue().appendFailed( *ecQueueIt );

				ecQueueIt = ecQueue->erase(ecQueueIt);
			}
			else
			{
				++ecQueueIt;
			}

		}
	}

	return( getExecutionQueue().hasResult() );
}


/**
 * REPORT
 */
void AbstractProcessorUnit::reportHeader(
		OutStream & os, const std::string & processQNID) const
{
	os << TAB << "FAM< " << processQNID << " > " << this->getNameID();

AVM_IF_DEBUG_FLAG( CONFIGURING )
	if( isWeakEnableFilter() )
	{
		os << " using as ";

		if( isStrongEnableFilter() )
		{
			os << "(PRE & POST)";
		}
		if( isEnablePrefilter() )
		{
			os << "PRE";
		}
		else if( isEnablePostfilter() )
		{
			os << "POST";
		}

		os << "-FILTER";
	}

	if( isWeakEnableProcess() )
	{
		os << (isWeakEnableFilter() ? " &" : " using" ) << " as ";

		if( isStrongEnableProcess() )
		{
			os << "(PRE & POST)";
		}
		else if( isEnablePreprocess() )
		{
			os << "PRE";
		}
		else if( isEnablePostprocess() )
		{
			os << "POST";
		}
		os << "-PROCESS";
	}
AVM_ENDIF_DEBUG_FLAG_AND( CONFIGURING )

	os << EOL;
}


void AbstractProcessorUnit::reportDefault(OutStream & os) const
{
	AVM_OS_VERBOSITY_MEDIUM( os )
			<< TAB << "FORMAL MODULE ANALYSIS< "
			<< ( isNamed() ? strFQN() : strUniqId() )
			<< " > DONE !!!"  << EOL_FLUSH;
}


////////////////////////////////////////////////////////////////////////////////
// PROCESSOR REQUEST API
////////////////////////////////////////////////////////////////////////////////

/**
 * REQUEUE_RESERVE
 */
void AbstractProcessorUnit::handleRequestRequeueReserveTable(
		WaitingStrategy & aWaitingStrategy,
		ListOfExecutionContext & aReserveQueue,
		std::uint8_t aWeightMin, std::uint8_t aWeightMax)
{
	aWaitingStrategy.smartPush( aReserveQueue );
}


////////////////////////////////////////////////////////////////////////////////
// PREFILTER REMOVE EC TOOLS
////////////////////////////////////////////////////////////////////////////////

std::size_t AbstractProcessorUnit::remove(ExecutionContext * anEC,
		OutStream & logger, const std::string & msg)
{
	std::size_t ecCount = 1; // 1 for sep::destroyElement( anEC );

	// First remove child
	if( anEC->hasNext() )
	{
		ExecutionContext::rw_child_iterator itEC = anEC->begin();
		for( ExecutionContext * tmpEC = nullptr ; itEC != anEC->end() ; )
		{
			tmpEC = (*itEC);

			tmpEC->setContainer( nullptr );

			itEC = anEC->eraseChildContext( itEC );

			ecCount += AbstractProcessorUnit::remove( tmpEC , logger , msg );
		}

		anEC->clearChildContext();
	}

	// Effective remove
	if( anEC->hasPrevious() )
	{
		anEC->getPrevious()->removeChildContext(anEC);
	}

	getSymbexEventManager().notifyEventDestroyCtx( anEC );


AVM_IF_DEBUG_LEVEL_GTE_MEDIUM
	logger << (( msg.empty() ) ? "A Plugin Processor remove the" : msg)
			<< " EC:> " << anEC->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_GTE_MEDIUM

	sep::destroyElement( anEC );

	return( ecCount );
}



////////////////////////////////////////////////////////////////////////////////
// FINAL SLICING TOOLS
////////////////////////////////////////////////////////////////////////////////

bool AbstractProcessorUnit::isSliceableContext(ExecutionContext & anEC) const
{
	return( anEC.noneInfo(*this) );
}


void AbstractProcessorUnit::computeLeafEC(
		const ListOfExecutionContext & listOfRootEC,
		ListOfExecutionContext & listOfLeafEC)
{
	ListOfExecutionContext tmpListOfEC;

	for( const auto & itRootEC : listOfRootEC )
	{
		if( itRootEC->isLeafNode() )
		{
			listOfLeafEC.append( itRootEC );
		}
		else
		{
			tmpListOfEC.append( itRootEC->getNext() );
		}
	}

	if( tmpListOfEC.nonempty() )
	{
		computeLeafEC(tmpListOfEC, listOfLeafEC);
	}
}


void AbstractProcessorUnit::slice(ListOfExecutionContext & listOfLeafEC)
{
AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << getParameterWObject()->getFullyQualifiedNameID()
			<< " :> CUT BACK" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

	while( listOfLeafEC.nonempty() )
	{
		slice(listOfLeafEC, listOfLeafEC.pop_last());
	}

AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_TRACE << getParameterWObject()->getFullyQualifiedNameID()
			<< " :> CUT BACK END ( count: " << mSliceCount << " )"
			<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
}

void AbstractProcessorUnit::slice(
		ListOfExecutionContext & listOfLeafEC,
		ExecutionContext * leafEC)
{
	if( (leafEC != nullptr) && leafEC->isLeafNode()
		&& isSliceableContext(* leafEC) )
	{
		ExecutionContext * containerEC = leafEC->getContainer();

		if( containerEC != nullptr )
		{
			ExecutionContext * tmpEC = nullptr;

			// Destroy des fils de theFatherEC sauf targetEC
			ExecutionContext::rw_child_iterator it = containerEC->begin();
			for( ; it != containerEC->end() ; )
			{
				tmpEC = (*it);
				if( tmpEC->isLeafNode() && isSliceableContext(* tmpEC) )
				{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	tmpEC->traceMinimum(AVM_OS_TRACE << "\t");
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

					it = containerEC->eraseChildContext(it);
					++mSliceCount;

					listOfLeafEC.remove(tmpEC);

					getSymbexEventManager().notifyEventDestroyCtx( tmpEC );

					sep::destroyElement( tmpEC );
				}
				else
				{
					++it;
				}
			}

			slice(listOfLeafEC, containerEC);
		}
	}
	else
	{
	}
}


} /* namespace sep */
