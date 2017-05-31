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

#include <fam/queue/WaitingStrategy.h>

#include <sew/SymbexDispatcher.h>
#include <sew/SymbexEngine.h>
#include <sew/SymbexEventManager.h>


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
const avm_uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_PROCESSOR[5] =
		{ 50 , 50 , 50 , 50 , 50 };

const avm_uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_MAIN_PROCESSOR[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_ACTIVE_COVERAGE_PROCESSOR[5] =
		{ 40 , 40 , 40 , 40 , 40 };

const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_PASSIVE_COVERAGE_PROCESSOR[5] =
		{ 60 , 60 , 60 , 60 , 60 };


const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_MAIN_PROCESSOR[5] =
		{ 0 , 0 , 0 , 0 , 0 };

const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_EXTENDER_PROCESSOR[5] =
		{ 10 , 10 , 10 , 10 , 10 };

const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_REDUNDANCY[5] =
		{ 100 , 100 , 100 , 100 , 100 };


const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_TRANSITION_COVERAGE[5] =
		{ 40 , 40 , 40 , 40 , 40 };

const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_HIT_OR_JUMP[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_FORMULA_COVERAGE[5] =
		{ 60 , 60 , 60 , 60 , 60 };

const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_MACHINE_COVERAGE[5] =
		{ 60 , 60 , 60 , 60 , 60 };


const avm_uint8_t AbstractProcessorUnit::PRECEDENCE_OF_TEST_OFFLINE[5] =
		{ 40 , 40 , 40 , 40 , 40 };


const avm_uint8_t AbstractProcessorUnit::DEFAULT_PRECEDENCE_OF_SERIALIZER_PROCESSOR[5] =
		{ 75 , 75 , 75 , 75 , 75 };


/**
 * CONSTRUCTOR
 * Default
 */
AbstractProcessorUnit::AbstractProcessorUnit(SymbexControllerUnitManager & aManager,
		WObject * wfParameterObject, avm_computing_process_stage_t requiredStage,
		const avm_uint8_t * aPrecedence)
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
mSliceCount( 0 ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( NULL ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}


AbstractProcessorUnit::AbstractProcessorUnit(SymbexControllerUnitManager & aManager,
		WObject * wfParameterObject, const avm_uint8_t * aPrecedence)
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
mSliceCount( 0 ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( NULL ),
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
		SymbexControllerUnitManager & aManager, WObject * wfParameterObject)
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
mSliceCount( 0 ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( NULL ),
ecQueueIt( ),
ecQueueItEnd( ),

ecChildIt( ),
ecChildItEnd( )
{
	//!! NOTHING
}

AbstractProcessorUnit::AbstractProcessorUnit(class_kind_t aClassKind,
		SymbexEngine & anEngine, SymbexControllerUnitManager & aManager,
		WObject * wfParameterObject)
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
mSliceCount( 0 ),

mPreEvalTraceFormatter( ),
mPostEvalTraceFormatter( ),

mBoundEvalTraceFormatter( ),
mReportEvalTraceFormatter( ),

////////////////////////////////////////////////////////////////////////////////
// Computing Variables
ecQueue( NULL ),
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

SymbexEventManager & AbstractProcessorUnit::getSymbexEventManager() const
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
	WObject * theCONFIG = getParameterWObject();

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

	// For Eval Trace format
	isOK = configureLog() && isOK;

	return( isOK );
}


bool AbstractProcessorUnit::configureLog()
{
	bool isOK = true;

	mPreEvalTraceFormatter = getDefaultPreEvalTraceFormatter();

	mPostEvalTraceFormatter = getDefaultPostEvalTraceFormatter();

	mBoundEvalTraceFormatter = getDefaultBoundEvalTraceFormatter();

	mReportEvalTraceFormatter = getDefaultReportEvalTraceFormatter();

	WObject * theLOG = Query::getWSequenceOrElse(
			getParameterWObject(), "console", "LOG");
	if( theLOG != WObject::_NULL_ )
	{
		mPreEvalTraceFormatter = Query::getWPropertyStringOrElse( theLOG,
				"step", "eval", Query::getWPropertyString( theLOG, "format",
						mPreEvalTraceFormatter) );

		StringTools::replaceAll(mPreEvalTraceFormatter, "\\t", "\t");
		StringTools::replaceAll(mPreEvalTraceFormatter, "\\n", "\n");


		mPostEvalTraceFormatter = Query::getWPropertyStringOrElse( theLOG,
				"result", "format", mPostEvalTraceFormatter );

		StringTools::replaceAll(mPostEvalTraceFormatter, "\\t", "\t");
		StringTools::replaceAll(mPostEvalTraceFormatter, "\\n", "\n");


		mBoundEvalTraceFormatter = Query::getWPropertyStringOrElse( theLOG,
				"bound", "format", mBoundEvalTraceFormatter );

		StringTools::replaceAll(mBoundEvalTraceFormatter, "\\t", "\t");
		StringTools::replaceAll(mBoundEvalTraceFormatter, "\\n", "\n");


		mReportEvalTraceFormatter = Query::getWPropertyStringOrElse( theLOG,
				"report", "format", mReportEvalTraceFormatter );

		StringTools::replaceAll(mReportEvalTraceFormatter, "\\t", "\t");
		StringTools::replaceAll(mReportEvalTraceFormatter, "\\n", "\n");
	}

	if( theLOG == NULL )
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
		mComputingStageEnabled = mComputingStageRequired;

//!![DEBUG]
//mProcessorManager.toStream(
//		AVM_OS_DEBUG << "before autoConfigureMOEImpl< " << this->strUniqId()
//				<< " >" << std::endl );

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

//!![DEBUG]
//mProcessorManager.toStream(
//		AVM_OS_DEBUG << std::endl << "after autoConfigureMOEImpl< "
//				<< this->strUniqId() << " >" << std::endl );
	}
	else
	{
		AVM_OS_DEBUG << "TODO autoConfigureMOEImpl< "
				<< this->strUniqId() << " >" << std::endl;
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
		OutStream & os, const std::string & processorName) const
{
	os << TAB << processorName << " PROCESSOR";

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
		avm_uint8_t aWeightMin, avm_uint8_t aWeightMax)
{
	aWaitingStrategy.pushChild( aReserveQueue );
}


////////////////////////////////////////////////////////////////////////////////
// PREFILTER REMOVE EC TOOLS
////////////////////////////////////////////////////////////////////////////////

avm_size_t AbstractProcessorUnit::remove(ExecutionContext * anEC,
		OutStream & logger, const std::string & msg)
{
	avm_size_t ecCount = 1; // 1 for sep::destroyElement( anEC );

	// First remove child
	if( anEC->hasNext() )
	{
		ExecutionContext::rw_child_iterator itEC = anEC->begin();
		for( ExecutionContext * tmpEC = NULL ; itEC != anEC->end() ; )
		{
			tmpEC = (*itEC);

			tmpEC->setContainer( NULL );

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

	ListOfExecutionContext::const_iterator itEC = listOfRootEC.begin();
	ListOfExecutionContext::const_iterator endEC = listOfRootEC.end();
	for( ; itEC != endEC ; ++itEC )
	{
		if( (*itEC)->isLeafNode() )
		{
			listOfLeafEC.append( *itEC );
		}
		else
		{
			tmpListOfEC.append( (*itEC)->getNext() );
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
	if( (leafEC != NULL) && leafEC->isLeafNode()
		&& isSliceableContext(* leafEC) )
	{
		ExecutionContext * containerEC = leafEC->getContainer();

		if( containerEC != NULL )
		{
			ExecutionContext * tmpEC = NULL;

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
