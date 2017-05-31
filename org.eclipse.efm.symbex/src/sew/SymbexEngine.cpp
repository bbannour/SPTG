/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 mars 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SymbexEngine.h"

#include <builder/Builder.h>
#include <parser/ParserManager.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/SymbexDispatcher.h>
#include <sew/Workflow.h>

#include <util/ExecutionTime.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
SymbexEngine::SymbexEngine(Workflow & aWorkflow,
		WObject * wfParameterObject, avm_offset_t anOffset)
: RunnableElement( wfParameterObject ),
mWorkflow( aWorkflow ),

mConfiguration( *this , mWorkflow ),
mPrimitiveProcessor( *this , mConfiguration ),

mBuilder( *this , mConfiguration  , mPrimitiveProcessor ),
mLoader( mConfiguration, mBuilder , mPrimitiveProcessor ),

mControllerUnitManager( *this , wfParameterObject ),
mSymbexDispatcher( *this , wfParameterObject , mControllerUnitManager),
mExecutionTimeManager( false ),

mOffset( anOffset ),

mPreviousEngine( NULL ),
mNextEngine( NULL )
{
	//!! NOTHING
}


/**
 * CONFIGURE
 */
bool SymbexEngine::configure()
{
	OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_COUT ) << _SEW_
			<< "Configure Engine director: " << strUniqId() << " ... START"
			<< std::endl;

	AVM_OS_LOG << _SEW_
			<< "Configure Engine director: " << strUniqId()
			<< std::endl;

	if( not mConfiguration.configure(getParameterWObject(),
		((mPreviousEngine != NULL) ? &(mPreviousEngine->mConfiguration) : NULL)) )
	{
		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

AVM_IF_DEBUG_FLAG( CONFIGURING )
	mConfiguration.toStream( AVM_OS_LOG );
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )

		return( false );
	}

AVM_IF_DEBUG_FLAG( CONFIGURING )
	mConfiguration.toStream( AVM_OS_LOG );
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )

	////////////////////////////////////////////////////////////////////////////
	///// PRIMITIVE PROCESSOR
	////////////////////////////////////////////////////////////////////////////

	if( not mPrimitiveProcessor.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine::configure:> "
					"the PrimitiveProcessor configuration failed !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	////////////////////////////////////////////////////////////////////////////
	///// BUILDER PROCESSOR
	////////////////////////////////////////////////////////////////////////////

	if( not mBuilder.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine::configure:> "
					"the Builder configuration failed !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	////////////////////////////////////////////////////////////////////////////
	///// LOADER PROCESSOR
	////////////////////////////////////////////////////////////////////////////

	if( not mLoader.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine::configure:> "
					"the Loader configuration failed !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	////////////////////////////////////////////////////////////////////////////
	///// PARSING
	////////////////////////////////////////////////////////////////////////////

	if( mConfiguration.hasOwnedSpecification() )
	{
		if( not startParsing() )
		{
AVM_IF_DEBUG_ENABLED_OR( mConfiguration.isDebugStageEnabled() )
	if( mConfiguration.hasSpecification() )
	{
		mConfiguration.saveSpecification( true , "parsing_failed" );
	}
AVM_ENDIF_DEBUG_ENABLED_OR

			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

			return( false );
		}

AVM_IF_DEBUG_ENABLED_OR( mConfiguration.isDebugParsingStageEnabled() )
	mConfiguration.saveSpecification( true , "parsed" );
AVM_ENDIF_DEBUG_ENABLED_OR

		////////////////////////////////////////////////////////////////////////
		///// BUILDING : COMPILING ; LOADING
		////////////////////////////////////////////////////////////////////////

		if( not startBuilding() )
		{
			mConfiguration.saveSpecification(true, "building");

			mConfiguration.serializeDebugExecutable( "building" );

			avm_set_exit_code( AVM_EXIT_COMPILING_ERROR_CODE );

			return( false );
		}

AVM_IF_DEBUG_FLAG_AND( COMPILING , mConfiguration.isDebugCompilingStageEnabled() )
	mConfiguration.serializeDebugExecutable( "built" );

	mConfiguration.saveSpecification( true , "built" );
AVM_ENDIF_DEBUG_FLAG_AND( COMPILING )
	}

	// Mandatory for expression compiling in any PluginProcessor
	else if( mPreviousEngine != NULL  )
	{
		mBuilder.getAvmcodeCompiler().getSymbolTable().setSymbolTable(
			mPreviousEngine->getBuilder().getAvmcodeCompiler().getSymbolTable() );

		mConfiguration.set( mPreviousEngine->mConfiguration );
	}
	else
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
				"No Specification in the first Engine Core !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	////////////////////////////////////////////////////////////////////////////
	///// CONTROLLER UNIT CONFIGURATION
	////////////////////////////////////////////////////////////////////////////

	if( not mControllerUnitManager.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
				"Failed to configure the Controller Unit Manager !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	if( not mSymbexDispatcher.configure() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
				"Failed to configure the Dispatcher !!!"
				<< SEND_ALERT;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}

	OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_COUT ) << _SEW_
			<< "Configure Engine director: " << strUniqId() << "... DONE"
			<< std::endl;

	return( true );
}


/**
 * INIT * PRE-PROCESS
 */
bool SymbexEngine::initImpl()
{
	if( not mControllerUnitManager.init() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
					"the Plugin Processor Manager initialisation failed !!!"
				<< SEND_ALERT;

		return( false );
	}


	if( not mSymbexDispatcher.init() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> the Engine initialisation failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


bool SymbexEngine::preprocess()
{
	bool isPreProcessor_OK = mControllerUnitManager.preprocess();

	while( mConfiguration.hasInputContext() )
	{
		if( mConfiguration.getInputContext().last()->isRoot() )
		{
			mConfiguration.appendTrace(
					mConfiguration.getInputContext().last() );
		}

		mControllerUnitManager.getExecutionQueue().appendInit(
				mConfiguration.getInputContext().pop_last() );
	}

	if( mConfiguration.noTrace() && (mPreviousEngine != NULL) )
	{
		mConfiguration.appendTrace(
				mPreviousEngine->mConfiguration.getTrace() );
	}

	bool isSymbexDispatcher_OK = mSymbexDispatcher.preprocess();

	bool isfilteringInitialize_OK = mControllerUnitManager.filteringInitialize();

	if( isPreProcessor_OK && isSymbexDispatcher_OK && isfilteringInitialize_OK )
	{
		mControllerUnitManager.getExecutionQueue().pushInit2Waiting();

		return true;
	}

	return false;
}


/**
 * START
 */
bool SymbexEngine::start()
{
	////////////////////////////////////////////////////////////////////////////
	///// COMPUTING
	////////////////////////////////////////////////////////////////////////////

	avm_report(AVM_OS_LOG, "SymbexEngine::startComputing");

	mExecutionTimeManager.start_time();

	mSymbexDispatcher.start();

	////////////////////////////////////////////////////////////////////////////
	///// EXECUTION TIME REPORT
	////////////////////////////////////////////////////////////////////////////

	mExecutionTimeManager.finish_time();

	AVM_OS_LOG << std::endl << mExecutionTimeManager.time_stat() << std::endl;
	AVM_OS_COUT << std::endl << mExecutionTimeManager.time_stat() << std::endl;

	return( true );
}


/**
 * POST-PROCESS
 */
bool SymbexEngine::postprocess()
{
	bool isfilteringFinalize_OK = mControllerUnitManager.filteringFinalize();

	bool isEngine_OK = mSymbexDispatcher.postprocess();

	bool isPostProcessor_OK = mControllerUnitManager.postprocess();

	return( isfilteringFinalize_OK && isEngine_OK && isPostProcessor_OK );
}


/**
 * EXIT
 */
bool SymbexEngine::exitImpl()
{
	if( not mControllerUnitManager.exit() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
					"the Plugin Processor Manager exit failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	if( not mSymbexDispatcher.exit() )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> the Engine exit failed !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}


/**
 * REPORT TRACE
 */
void SymbexEngine::preReport(OutStream & os) const
{
	//!! NOTHING
}

void SymbexEngine::dynReport(OutStream & os) const
{
	//!! NOTHING
}

void SymbexEngine::postReport(OutStream & os) const
{
	mSymbexDispatcher.report(AVM_OS_LOG);
	mSymbexDispatcher.report(AVM_OS_COUT);

	mControllerUnitManager.report(AVM_OS_LOG);
	mControllerUnitManager.report(AVM_OS_COUT);
}


void SymbexEngine::report(OutStream & os) const
{
	preReport(os);

	dynReport(os);

	postReport(os);
}


/**
 * PARSING
 *
 */
bool SymbexEngine::startParsing()
{
	AVM_OS_LOG << std::endl << _SEW_ << "< start > Parsing ..." << std::endl;

	ParserManager aParser( mConfiguration.getSpecificationFileLocation() );

	mConfiguration.setSpecification( aParser.parseFML(
			mConfiguration.getWObjectManager() ) );

	bool isOK = mConfiguration.hasSpecification() && aParser.hasNoSyntaxError();

	AVM_OS_LOG << _SEW_
			<< "< end > Parsing ... " << ( isOK ? "done." : "failed." )
			<< std::endl;

	return( isOK );
}


/**
 * BUILDING
 *
 */
bool SymbexEngine::startBuilding()
{
	AVM_OS_LOG << std::endl << _SEW_ << "< start > Building ..." << std::endl;

	bool isOK = mBuilder.start();

	serializeBuildingResult();

	AVM_OS_LOG << _SEW_
			<< "< end > Building ... " << ( isOK ? "done." : "failed." )
			<< std::endl;

	return( isOK );
}


/**
 * COMPUTING
 */
bool SymbexEngine::startComputing()
{
	AVM_OS_LOG << std::endl << _SBX_ << "< start > Computing ..." << std::endl;
	try
	{
		////////////////////////////////////////////////////////////////////////
		///// INITIALIZATION
		////////////////////////////////////////////////////////////////////////

		if( not init() )
		{
			avm_set_exit_code( AVM_EXIT_INITIALIZING_ERROR_CODE );

			return( false );
		}

		////////////////////////////////////////////////////////////////////////
		///// PRE PROCESSING
		////////////////////////////////////////////////////////////////////////

		if( not preprocess() )
		{
			avm_set_exit_code( AVM_EXIT_PRE_PROCESSING_ERROR_CODE );

			return( false );
		}

		////////////////////////////////////////////////////////////////////////
		///// REPORTING
		////////////////////////////////////////////////////////////////////////

		AVM_OS_LOG << std::endl;

		preReport(AVM_OS_LOG);

		AVM_OS_LOG << std::endl;

		////////////////////////////////////////////////////////////////////////
		///// START
		////////////////////////////////////////////////////////////////////////

		if( not start() )
		{
			avm_set_exit_code( AVM_EXIT_PROCESSING_ERROR_CODE );

			return( false );
		}

		////////////////////////////////////////////////////////////////////////
		///// REPORTING
		////////////////////////////////////////////////////////////////////////

		AVM_OS_LOG << std::endl;

		dynReport(AVM_OS_LOG);

		AVM_OS_LOG << std::endl;

		////////////////////////////////////////////////////////////////////////
		///// POST PROCESSING
		////////////////////////////////////////////////////////////////////////

		if( not postprocess() )
		{
			serializeComputingResult();

			avm_set_exit_code( AVM_EXIT_POST_PROCESSING_ERROR_CODE );

			return( false );
		}

		////////////////////////////////////////////////////////////////////////
		///// REPORTING
		////////////////////////////////////////////////////////////////////////

		AVM_OS_LOG << std::endl;

		postReport(AVM_OS_LOG);

		AVM_OS_LOG << std::endl;


		////////////////////////////////////////////////////////////////////////
		///// EXITING
		////////////////////////////////////////////////////////////////////////

		if( not exit() )
		{
			serializeComputingResult();

			avm_set_exit_code( AVM_EXIT_FINALIZING_ERROR_CODE );

			return( false );
		}

		////////////////////////////////////////////////////////////////////////
		///// REPORTING
		////////////////////////////////////////////////////////////////////////

//		AVM_OS_LOG << std::endl;
//
//		report(AVM_OS_LOG);
//
//		AVM_OS_LOG << std::endl;


		////////////////////////////////////////////////////////////////////////
		///// TEST DRIVEN DEVELOPMENT
		////////////////////////////////////////////////////////////////////////

		tddStart();

		////////////////////////////////////////////////////////////////////////
		///// SERIALIZATION
		////////////////////////////////////////////////////////////////////////

		serializeComputingResult();
	}
	catch ( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"SymbexEngine::startComputing< std::exception >",
				e.what(), '*', 80);

		AVM_OS_WARN << EMPHASIS("Save Point ...", '*', 80);

		////////////////////////////////////////////////////////////////////////
		///// FAILED REPORTING
		////////////////////////////////////////////////////////////////////////

		failedReport();
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"SymbexEngine::startComputing< unknown::exception > !!!",
				'*', 80);

		AVM_OS_WARN << EMPHASIS("Save Point ...", '*', 80);

		////////////////////////////////////////////////////////////////////////
		///// FAILED REPORTING
		////////////////////////////////////////////////////////////////////////

		failedReport();
	}

	AVM_OS_LOG << std::endl << _SBX_ << "< end > Computing ... done." << std::endl;

	return( true );
}


/**
 * Serialization
 */
void SymbexEngine::serializeBuildingResult()
{
	mConfiguration.serializeBuildingResult();
}

void SymbexEngine::serializeComputingResult()
{
	mConfiguration.serializeComputingResult();
}



void SymbexEngine::failedReport()
{
	////////////////////////////////////////////////////////////////////////////
	///// EXECUTION TIME REPORT
	////////////////////////////////////////////////////////////////////////////

	mExecutionTimeManager.finish_time();

	AVM_OS_LOG << std::endl << mExecutionTimeManager.time_stat() << std::endl;
	AVM_OS_COUT << std::endl << mExecutionTimeManager.time_stat() << std::endl;

	////////////////////////////////////////////////////////////////////////////
	///// REPORTING
	////////////////////////////////////////////////////////////////////////////

	AVM_OS_LOG << std::endl;

	report(AVM_OS_LOG);

	AVM_OS_LOG << std::endl;

	////////////////////////////////////////////////////////////////////////////
	///// SERIALIZATION
	////////////////////////////////////////////////////////////////////////////

	serializeComputingResult();
}


////////////////////////////////////////////////////////////////////////////////
// TEST DRIVEN DEVELOPMENT
////////////////////////////////////////////////////////////////////////////////

// TEST DRIVEN DEVELOPMENT
//section TDD
//	@report = "avm.tdd";
//
//	@regression = true;
//	@unit = true;
//endsection TDD

void SymbexEngine::tddStart()
{
	AVM_OS_TDD << "@tdd< version , 1.0 >: // "
			<< ExecutionTime::current_time() << std::endl;

	AVM_OS_TDD << "engine " << getParameterWObject()->getFullyQualifiedNameID() << std::endl;

	AVM_OS_TDD << INCR_INDENT;

	AVM_OS_TDD << "time#stat = " << mExecutionTimeManager.time_stat()
			<< std::endl;

	if( mWorkflow.isTddUnitTesting() )
	{
		tddUnitReport(AVM_OS_TDD);
	}

	if( mWorkflow.isTddRegressionTesting() )
	{
		tddRegressionReport(AVM_OS_TDD);
	}

	AVM_OS_TDD << DECR_INDENT;
	AVM_OS_TDD << "// end engine "
			<< getParameterWObject()->getFullyQualifiedNameID()
			<< std::endl << std::endl;
}

////////////////////////////////////////////////////////////////////////////////
// UNIT TEST API
////////////////////////////////////////////////////////////////////////////////

void SymbexEngine::tddUnitReport(OutStream & os) const
{
	AVM_OS_TDD << "@tdd< unit , 1.0 >:" << std::endl;

	mControllerUnitManager.tddUnitReport(os);
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void SymbexEngine::tddRegressionReport(OutStream & os) const
{
	AVM_OS_TDD << "@tdd< regression , 1.0 >:" << std::endl;

	mControllerUnitManager.tddRegressionReport(os);
}



}
