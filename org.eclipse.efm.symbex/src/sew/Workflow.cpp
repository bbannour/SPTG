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

#include "Workflow.h"

#include <builder/primitive/CompilationEnvironment.h>

#include <collection/List.h>
#include <collection/Typedef.h>

#include <computer/PathConditionProcessor.h>

#include <fml/runtime/ExecutionContext.h>

#include <parser/ParserManager.h>

#include <printer/Manipulators.h>
#include <printer/OutStream.h>

#include <sew/Configuration.h>
#include <sew/SymbexEngine.h>

#include <solver/api/SolverDef.h>

#include <util/avm_debug.h>
#include <util/avm_util.h>

#include <iostream>
#include <list>
#include <string>



namespace sep
{


/**
 * GLOBALS
 */
const std::string & Workflow::SECTION_WORKSPACE_REGEX_ID =
		OR_WID3( "workspace" , "WORKSPACE" , "LOCATION" );

const std::string & Workflow::SECTION_CONSOLE_REGEX_ID =
		OR_WID3( "console" , "CONSOLE" , "AVM" );

const std::string & Workflow::SECTION_DEVELOPER_REGEX_ID =
		OR_WID3( "developer" , "DEVELOPER" , "TRACE");

const std::string & Workflow::SECTION_DIRECTOR_REGEX_ID =
		OR_WID4( "director" , "DIRECTOR" , "MOC" , "RUNTIME");

const std::string & Workflow::SECTION_SHELL_REGEX_ID =
		OR_WID3( "shell" , "SHELL" , "AVM");

const std::string & Workflow::SECTION_SYMBEX_REGEX_ID =
		OR_WID3( "symbex" , "SYMBEX" , "AVM");

const std::string & Workflow::SECTION_TDD_REGEX_ID =
		OR_WID2( "tdd" , "TDD");


const std::string & Workflow::SECTION_FAM_REGEX_ID =
		OR_WID2(OR_WID4( "controller" , "worker" , "processor" , "filter" ),
				OR_WID4( "CONTROLLER" , "WORKER" , "PROCESSOR" , "FILTER" ));


const std::string & Workflow::SECTION_FAM_CONTAINERS_REGEX_ID =
		OR_WID4(OR_WID4( "controller" , "worker" , "processor" , "filter" ),
				OR_WID4( "CONTROLLER" , "WORKER" , "PROCESSOR" , "FILTER" ),
				OR_WID3( "queue" , "pre_process" , "post_process" ),
				OR_WID3( "QUEUE" , "PRE_PROCESS" , "POST_PROCESS" ));

// Deprecated
const std::string & Workflow::SECTION_FAM_QUEUE_REGEX_ID =
		OR_WID2( "queue" , "QUEUE" );

const std::string & Workflow::SECTION_FAM_REDUNDANCY_REGEX_ID =
		OR_WID2( "redundancy" , "REDUNDANCY" );

const std::string & Workflow::SECTION_FAM_PROCESSOR_REGEX_ID =
		OR_WID2(OR_WID3( "controller" , "worker" , "processor" ),
				OR_WID3( "CONTROLLER" , "WORKER" , "PROCESSOR" ));

const std::string & Workflow::SECTION_FAM_FILTER_REGEX_ID =
		OR_WID2( "filter" , "FILTER" );

const std::string & Workflow::SECTION_FAM_PREPROCESS_REGEX_ID =
		OR_WID2( "pre_process" , "PRE_PROCESS" );

const std::string & Workflow::SECTION_FAM_POSTPROCESS_REGEX_ID =
		OR_WID2( "post_process" , "POST_PROCESS" );


/**
 * SINGLETON
 */
Workflow * Workflow::INSTANCE = NULL;


/**
 * LOADER
 */
bool Workflow::load()
{
	return( true );
}


/**
 * DISPOSER
 */
void Workflow::dispose()
{
	mCurrentSymbexEngine = mMainSymbexEngine;
	for( ; mCurrentSymbexEngine != NULL ; mCurrentSymbexEngine = mMainSymbexEngine )
	{
		mMainSymbexEngine = mMainSymbexEngine->getNextCore();

		sep::destroy( mCurrentSymbexEngine );

		mCurrentSymbexEngine = NULL;
	}
}


////////////////////////////////////////////////////////////////////////////////
///// AVM CONFIGURATION PARAMETER CHECKER
////////////////////////////////////////////////////////////////////////////////

bool Workflow::loadConfiguration(const std::string & aWorkflowLocation)
{
	mSEWFileLocation = aWorkflowLocation;

	// Checking WORKFLOW
	AVM_OS_COUT << _SEW_
			<< "Symbolic Execution based Workflow analysis ... START"
			<< std::endl
			<< _SEW_ << "Location: " << mSEWFileLocation << std::endl;

	// Load workflow definition file
	if( parseConfiguration() )
	{
		AVM_OS_COUT << _SEW_ << "Loading filename: \""
				<< VFS::filename( mSEWFileLocation )
				<< "\" ... done !" << std::endl;
	}
	else
	{
		return( false );
	}

	bool isOK = true;

	StringOutStream OS_INIT_LOG;

	// Configure core elements
	isOK = loadCoreElementsConfig(OS_INIT_LOG);

	// Set developer debug options
	isOK = loadWorkspaceLocationsConfig(OS_INIT_LOG) && isOK;

	// Initialize log & debug trace printers
	isOK = isOK && OutStream::configure(this);

AVM_IF_DEBUG_LEVEL_FLAG2_AND(HIGH , PARSING , CONFIGURING ,
		(mParameterWObject != WObject::_NULL_) )

	std::string parseResultFile = VFS::suffixFilename(
			VFS::filename( mSEWFileLocation ), "_parsed", ".sew");

	parseResultFile = VFS::native_path(parseResultFile,
			VFS::WorkspaceDebugPath.empty()
					? VFS::parent( mSEWFileLocation )
					: VFS::WorkspaceDebugPath );

	OS_INIT_LOG << _DBG_ << "Saving of the parsed Workflow in text format ..."
			<< std::endl;

	Configuration::saveElementTextualView(
			OS_INIT_LOG, mParameterWObject, parseResultFile);

AVM_ENDIF_DEBUG_LEVEL_FLAG_AND(ULTRA , PARSING )

	if( isOK )
	{
		AVM_OS_LOG << _SEW_ << "Symbolic Execution "
				"based Workflow analysis ... START"
				<< std::endl
				<< _SEW_ << "Location: " << mSEWFileLocation
				<< std::endl;

		OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_COUT )
				<< OS_INIT_LOG.str() << std::flush;

		AVM_OS_LOG << OS_INIT_LOG.str() << std::flush;
	}
	else
	{
		AVM_OS_COUT << OS_INIT_LOG.str() << std::flush;

		return( false );
	}

	// Set developer debug options
	isOK = loadSymbexConfig() && isOK;

	isOK = loadShellConfig() && isOK;

	isOK = loadTddConfig() && isOK;

	isOK = loadOthersConfig() && isOK;

	if( isOK )
	{
		avm_report(AVM_OS_LOG, "Workflow::loadConfiguration:> "
				"end of avm configuration checking !!!");
	}
	else
	{
		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );
	}

	AVM_OS_COUT << _SEW_
			<< "Symbolic Execution based Workflow analysis ... "
			<< ( isOK ? "DONE" : "FAILED !" )
			<< std::endl << std::endl;

	AVM_OS_LOG << _SEW_
			<< "Symbolic Execution Workflow analysis ... "
			<< ( isOK ? "DONE" : "FAILED !" )
			<< std::endl << std::endl;

	return( isOK );
}


/**
 * Load workflow definition file
 */
bool Workflow::parseConfiguration()
{
	std::ifstream anInputStream( mSEWFileLocation.c_str() );

	if( anInputStream.good() )
	{
		std::string antlrExceptionMsg;

		ParserManager aParser( mSEWFileLocation );

		mParameterWObject = aParser.parseSEW(mWObjectManager, anInputStream );

		if( aParser.hasSyntaxError() )
		{
			AVM_OS_CERR << std::endl;

			if( aParser.hasExceptionMessage() )
			{
				AVM_OS_CERR << _SEW_ << "< exception > "
						<< aParser.getExceptionMessage() << std::endl;
			}

			AVM_OS_CERR << std::endl << _SEW_ << "< error > "
					<< aParser.getErrorCount() << " syntax error"
					<< ((aParser.getErrorCount() > 1)? "s" : "")
					<< " found." << std::endl;

			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

			return( false );
		}
		else if( mParameterWObject == WObject::_NULL_ )
		{
			AVM_OS_CERR << _SEW_ << "< error > No parsing result !"
					<< std::endl;

			avm_set_exit_code( AVM_EXIT_PARSING_ERROR_CODE );

			return( false );
		}
		else
		{
			return( true );
		}
	}
	else
	{
		AVM_OS_CERR << _SEW_ << "< error > Cannot open the file \""
				<< VFS::filename(mSEWFileLocation) << "\" !"
				<< std::endl << std::endl;

		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );

		return( false );
	}
}


/**
 * Configure core elements
 * Set console verbosity level
 * Set developer debug level
 * Set developer debug flags
 */
/*
section CONSOLE // @deprecated AVM
	verbosity = 'MINIMUM'; // SILENT == MINIMUM < MEDIUM < MAXIMUM
endsection CONSOLE

section DEVELOPER // @deprecated TRACE
	level = 'ZERO'; // ZERO < LOW < MEDIUM < HIGH < ULTRA

	flag = 'PARSING'; --> @deprecated kind = 'PARSING';
	flag = 'COMPILING';
	flag = 'STATEMENT';
	flag = 'BYTECODE';
endsection DEVELOPER
*/
bool Workflow::loadCoreElementsConfig(OutStream & LOGGER)
{
	// Set console verbosity level
	avm_setExecVerbosityLevel(
			Query::getRegexWPropertyString(
					getCONSOLE(), "verbos(ity|e)", "MAXIMUM") );

	// DEVELOPER
	WObject * configDEVELOPER = getDEVELOPER();

	// Set developer debug level
	avm_setDebugLevel(
			Query::getWPropertyString(configDEVELOPER, "level", "ZERO") );

	// Set developer debug flags
	ListOfString listOfFlags;
	Query::getWPropertyString(configDEVELOPER, "flag", "kind",listOfFlags);

	if( listOfFlags.nonempty() )
	{
		ListOfString::iterator it = listOfFlags.begin();

		avm_setDebugFlag(*it);

		for( ++it ; it != listOfFlags.end() ; ++it )
		{
			avm_setDebugFlag(*it);
		}
	}

	OS_VERBOSITY_MINIMUM_OR_DEBUG( LOGGER )
			<< _SEW_ << "Console verbosity level: \'"
			<< avm_strExecVerbosityLevel() << "\'"
			<< std::endl;

AVM_IF_DEBUG_ENABLED

	LOGGER << _SEW_ << "Developer debug level: \'"
			<< avm_strDebugLevel() << "\'"
			<< std::endl;

	LOGGER << _SEW_ << "Developer debug flags: \'"
			<< avm_strDebugFlag(" | ") << "\'"
			<< std::endl;

AVM_ENDIF_DEBUG_ENABLED

	return( true );
}

/**
 * configure workspace location & folders
 * root location
 * source folder
 * output folder
 * log folder
 * debug folder
 * tdd folder
 */
/*
section WORKSPACE // @deprecated LOCATION
	root = "<workspace-root-path>";
	project = "<project-root-path>"; //# DEPRECATED

	source = ".";

	output = "output";
	log = "log";
	debug = "debug";

	tdd = "tdd";
endsection WORKSPACE
 */
bool Workflow::loadWorkspaceLocationsConfig(OutStream & LOGGER)
{
	bool isOK = true;

	/*
	 * CHECKING FILE AND FOLDER
	 */
	LOGGER << _SEW_ << "The launch folder: "
			<< VFS::LaunchPath << std::endl;

	WObject * configWORKSPACE = getWORKSPACE();

	VFS::ProjectPath = VFS::WorkspaceRootPath =
			VFS::native_path(
					Query::getWPropertyStringOrElse(
							configWORKSPACE, "root", "project", "."),
					VFS::LaunchPath);

	LOGGER << _SEW_ << "The <wroot> folder: "
			<< VFS::WorkspaceRootPath << std::endl;

	if( VFS::checkReadingFolder(VFS::WorkspaceRootPath) )
	{
		VFS::ProjectSourcePath = VFS::WorkspaceSourcePath =
				VFS::native_path(
						Query::getWPropertyStringOrElse(
								configWORKSPACE, "source", "src", "."),
						VFS::WorkspaceRootPath);

		LOGGER << _SEW_ << "The source! folder: "
				<< VFS::relativeWorkspacePath( VFS::WorkspaceSourcePath )
				<< std::endl;
		if( not VFS::checkWritingFolder(VFS::WorkspaceSourcePath) )
		{
			LOGGER << _SEW_ << "< error > The source folder `"
					<< VFS::filename( VFS::WorkspaceSourcePath )
					<< "' ==> doesn't exist or is not writable !!!"
					<< std::endl << std::endl;

			isOK = false;
		}

		VFS::ProjectOutputPath = VFS::WorkspaceOutputPath =
				VFS::native_path(
						Query::getWPropertyStringOrElse(
								configWORKSPACE, "output", "out", "out"),
						VFS::WorkspaceRootPath);

		LOGGER << _SEW_ << "The output! folder: "
				<< VFS::relativeWorkspacePath( VFS::WorkspaceOutputPath )
				<< std::endl;
		if( not VFS::checkWritingFolder(VFS::WorkspaceOutputPath) )
		{
			LOGGER << _SEW_ << "< error > The folder `"
					<< VFS::filename( VFS::WorkspaceOutputPath )
					<< "' ==> doesn't exist or is not writable !!!"
					<< std::endl << std::endl;

			isOK = false;
		}

		if( needDeveloperDebugLogTraceFolder() )
		{
			VFS::ProjectLogPath = VFS::WorkspaceLogPath =
					VFS::native_path(
							Query::getWPropertyString(
									configWORKSPACE, "log", "log"),
							VFS::WorkspaceOutputPath);

			LOGGER << _SEW_ << "The logger! folder: "
					<< VFS::relativeWorkspacePath( VFS::WorkspaceLogPath )
					<< std::endl;
			if( not VFS::checkWritingFolder(VFS::WorkspaceLogPath) )
			{
				LOGGER << _SEW_ << "< error > The folder `"
						<< VFS::filename( VFS::WorkspaceLogPath )
						<< "' ==> doesn't exist or is not writable !!!"
						<< std::endl << std::endl;

				isOK = false;
			}
		}
		else if( isOK )
		{
			VFS::ProjectLogPath =
					VFS::WorkspaceLogPath =
							VFS::WorkspaceOutputPath;
		}

		VFS::ProjectDebugPath =
				VFS::WorkspaceDebugPath =
						VFS::WorkspaceLogPath;

AVM_IF_DEBUG_ENABLED
	VFS::ProjectDebugPath = VFS::WorkspaceDebugPath =
			VFS::native_path(
					Query::getWPropertyStringOrElse(
							configWORKSPACE, "debug", "dbg", "debug"),
					VFS::WorkspaceOutputPath);

	LOGGER << _SEW_ << "The !debug! folder: "
			<< VFS::relativeWorkspacePath( VFS::WorkspaceDebugPath )
			<< std::endl;
	if( not VFS::checkWritingFolder(VFS::WorkspaceDebugPath) )
	{
		LOGGER << _SEW_ << "< error > The folder `"
				<< VFS::filename( VFS::WorkspaceDebugPath )
				<< "' ==> doesn't exist or is not writable !!!"
				<< std::endl << std::endl;

		isOK = false;
	}
AVM_ENDIF_DEBUG_ENABLED

		if( hasTddReport() )
		{
			VFS::ProjectTddPath = VFS::WorkspaceTddPath =
					VFS::native_path(
							Query::getWPropertyString(
									configWORKSPACE, "tdd", "tdd"),
							VFS::WorkspaceRootPath);

			LOGGER << _SEW_ << "The tdd folder   : "
					<< VFS::relativeWorkspacePath( VFS::WorkspaceTddPath )
					<< std::endl;
			if( not VFS::checkWritingFolder(VFS::WorkspaceTddPath) )
			{
				LOGGER << _SEW_ << "< error > The folder `"
						<< VFS::filename( VFS::WorkspaceTddPath )
						<< "' ==> doesn't exist or is not writable !!!"
						<< std::endl << std::endl;

				isOK = false;
			}
		}
	}
	else
	{
		LOGGER << _SEW_
				<< "< error > The <wroot> folder location "
				"==> doesn't exist or is not Readable !!!"
				<< std::endl << std::endl;

		isOK = false;
	}

	return( isOK );
}

/*
section SYMBEX // @deprecated AVM
	mode = 'standalone'; // standalone | server | interactive | debug

	multithread = false;
	thread = 2;
endsection SYMBEX
*/
bool Workflow::loadSymbexConfig()
{
	WObject * configSYMBEX = getSYMBEX();

	PathConditionProcessor::checkPathcondSat =
		SolverDef::DEFAULT_SOLVER_USAGE_FLAG =
			Query::getRegexWPropertyBoolean(configSYMBEX,
				CONS_WID4("check", "path", "condition", "satisfiability"),
				false);

	PathConditionProcessor::separationOfPcDisjunction =
			Query::getWPropertyBoolean(configSYMBEX,
					"separation_of_pc_disjunction", false);


	std::string solverKind = Query::getRegexWPropertyString(
			configSYMBEX, CONS_WID2("constraint", "solver"), "CVC");

	SolverDef::DEFAULT_SOLVER_KIND = SolverDef::toSolver(solverKind,
			SolverDef::SOLVER_CVC_KIND);

AVM_IF_DEBUG_ENABLED
	AVM_OS_LOG << _SEW_ << "The default solver: < checksat="
			<< ( SolverDef::DEFAULT_SOLVER_USAGE_FLAG ? "true" : "false" )
			<< " , " << solverKind << " > |=> "
			<< SolverDef::strSolver(SolverDef::DEFAULT_SOLVER_KIND)
			<< std::endl;
AVM_ENDIF_DEBUG_ENABLED

	mMultitaskingFlag =
			Query::getWPropertyBoolean(configSYMBEX, "multitasking", false);

	mThreadCount = Query::getWPropertyInt(configSYMBEX, "thread", 2);

	std::string evalMode = Query::getWPropertyString(configSYMBEX, "mode", "");

AVM_IF_DEBUG_ENABLED
	AVM_OS_LOG << _SEW_ << "Computing resource: < multitasking="
			<< ( ( mMultitaskingFlag ) ? "true" : "false" )
			<< " , thread=" << static_cast< unsigned int >( mThreadCount )
			<< " >" << std::endl;
AVM_ENDIF_DEBUG_ENABLED

	return( true );
}


/*
section SHELL // Deprecated AVM
	stop = "stop.avm";
endsection SHELL
*/
bool Workflow::loadShellConfig()
{
	WObject * configSHELL = getSHELL();

	mInconditionalStopMarkerLocation = VFS::native_path(
			Query::getWPropertyString(configSHELL, "stop", "stop.sew"));

	mInconditionalStopMarkerLocation = VFS::native_path(
			mInconditionalStopMarkerLocation, VFS::WorkspaceLogPath);

	return( true );
}


/**
 * Other Elements Configuration
 */
bool Workflow::loadTddConfig()
{
	mTddRegressionTestingFlag =
			Query::getWPropertyBoolean(getTDD(), "regression", false);

	mTddUnitTestingFlag = Query::getWPropertyBoolean(getTDD(), "unit", false);

	return( true );
}


/**
 * Other Elements Configuration
 */
bool Workflow::loadOthersConfig()
{
	ExecutionContext::EXECUTION_CONTEXT_CHILD_TRACE_MAX =
			Query::getWPropertyLong(getCONSOLE(), "ec_size",
					ExecutionContext::EXECUTION_CONTEXT_CHILD_TRACE_MAX);

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool Workflow::configure()
{
	mMainSymbexEngine = NULL;

	WObject * sequenceDIRECTOR = getDIRECTOR();

	const BF & mocRuntime =
			Query::getWPropertyValueOrElse(sequenceDIRECTOR, "moe", "moc");

	avm_offset_t anEngineOffset = 0;

	if( WObjectManager::is( mocRuntime ) )
	{
		mMainSymbexEngine = new SymbexEngine(*this,
				WObjectManager::from( mocRuntime ), anEngineOffset++);

		if(not  mMainSymbexEngine->configure() )
		{
			delete( mMainSymbexEngine );

			mMainSymbexEngine = NULL;

			return( false );
		}
	}
	else if( mocRuntime.is< AvmCode >() )
	{
		SymbexEngine * nextEngine = NULL;
		SymbexEngine * prevEngine = NULL;

		AvmCode::iterator itEngine = mocRuntime.to_ptr< AvmCode >()->begin();
		AvmCode::iterator itEnd = mocRuntime.to_ptr< AvmCode >()->end();
		for( ; itEngine != itEnd ; ++itEngine )
		{
			if( WObjectManager::is( *itEngine ) )
			{
				nextEngine = new SymbexEngine(*this,
						WObjectManager::from( *itEngine ), anEngineOffset++);

				nextEngine->setPreviousCore( prevEngine );

				if( nextEngine->configure() )
				{
					if( mMainSymbexEngine == NULL )
					{
						mMainSymbexEngine = nextEngine;
					}

					if( prevEngine != NULL )
					{
						prevEngine->setNextCore( nextEngine );
					}
					prevEngine = nextEngine;
				}
				else
				{
					delete( nextEngine );

					return( false );
				}
			}
			else
			{
				return( false );
			}
		}
	}
	else
	{
		SymbexEngine * nextEngine = NULL;
		SymbexEngine * prevEngine = NULL;

		List< WObject * > engineList;
		Query::getListWObject(sequenceDIRECTOR, engineList);

		List< WObject * >::iterator itForm = engineList.begin();
		for( ; itForm != engineList.end() ; ++itForm )
		{
			nextEngine = new SymbexEngine(*this, *itForm, anEngineOffset++ );

			nextEngine->setPreviousCore( prevEngine );

			if( nextEngine->configure() )
			{
				if( mMainSymbexEngine == NULL )
				{
					mMainSymbexEngine = nextEngine;
				}

				if( prevEngine != NULL )
				{
					prevEngine->setNextCore( nextEngine );
				}
				prevEngine = nextEngine;
			}
			else
			{
				delete( nextEngine );

				return( false );
			}
		}
	}

	return( true );
}


/**
 * Prologue options
 */
void Workflow::setPrologueOption(
		const std::string & id, BF value)
{
	if( REGEX_MATCH(id, CONS_WID2("check", "type")) )
	{
		COMPILE_CONTEXT::DEFAUL_TYPE_CHECKING_MASK = value.isNotEqualFalse();
	}

	else if( REGEX_MATCH(id, CONS_WID2("inline", "disable")) )
	{
		COMPILE_CONTEXT::INLINE_DISABLE_MASK = value.isNotEqualFalse();
	}
	else if( REGEX_MATCH(id, CONS_WID2("inline", "enable")) )
	{
		COMPILE_CONTEXT::INLINE_ENABLE_MASK = value.isNotEqualFalse();
	}

	else if( REGEX_MATCH(id, CONS_WID2("inline", "procedure")) )
	{
		COMPILE_CONTEXT::INLINE_PROCEDURE_MASK = value.isNotEqualFalse();
	}

	else if( REGEX_MATCH(id, CONS_WID2("string", "delimiter")) )
	{
		if( value.isCharacter() )
		{
			String::_EMPTY_.to_ptr< String >()->setQuoteChar(
					String::DEFAULT_DELIMITER = value.toCharacter() );
		}
		else if( value.isBuiltinString() )
		{
			std::string delim = value.toBuiltinString();

			String::_EMPTY_.to_ptr< String >()->setQuoteChar(
					String::DEFAULT_DELIMITER =
							( delim.empty() ? '\0' : delim[0] ) );
		}
	}
}


/**
 * START
 */
bool Workflow::start()
{
	////////////////////////////////////////////////////////////////////////////
	///// START SEQUENTIALLY ENGINE CORE
	////////////////////////////////////////////////////////////////////////////

	for( mCurrentSymbexEngine = mMainSymbexEngine ; mCurrentSymbexEngine != NULL ;
			mCurrentSymbexEngine = mCurrentSymbexEngine->getNextCore() )
	{
		if( not mCurrentSymbexEngine->startComputing() )
		{
			return( false );
		}
	}

	return( true );
}


/**
 * EXIT
 */
bool Workflow::exitImpl()
{
//	bool isCasManager_OK =  mAvmConfiguration.getCasManager().exit();
//
//	return( RunnableElement::exit() && isCasManager_OK );

	return( true );
}


/**
 * REPORT TRACE
 */
void Workflow::report(OutStream & os) const
{
//	mAvmConfiguration.getCasManager().report(os);
//
//	mAvmConfiguration.getCasManager().report(AVM_OS_COUT);
}


/**
 * COMPUTING
 *
 */
bool Workflow::startComputing()
{
	AVM_OS_LOG << std::endl << _SEW_ << "< start > Computing ..." << std::endl;

	////////////////////////////////////////////////////////////////////////////
	///// INITIALIZATION
	////////////////////////////////////////////////////////////////////////////

	if( not init() )
	{
		avm_set_exit_code( AVM_EXIT_INITIALIZING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// PRE PROCESSING
	////////////////////////////////////////////////////////////////////////////

	if( not preprocess() )
	{
		avm_set_exit_code( AVM_EXIT_PRE_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// START
	////////////////////////////////////////////////////////////////////////////

	if( not start() )
	{
		avm_set_exit_code( AVM_EXIT_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// POST PROCESSING
	////////////////////////////////////////////////////////////////////////////

	if( not postprocess() )
	{
		avm_set_exit_code( AVM_EXIT_POST_PROCESSING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// EXITING
	////////////////////////////////////////////////////////////////////////////

	if( not exit() )
	{
		avm_set_exit_code( AVM_EXIT_FINALIZING_ERROR_CODE );

		return( false );
	}


	////////////////////////////////////////////////////////////////////////////
	///// REPORTING
	////////////////////////////////////////////////////////////////////////////

	AVM_OS_LOG << std::endl;

	report(AVM_OS_LOG);

	AVM_OS_LOG << std::endl;


	////////////////////////////////////////////////////////////////////////////
	///// SERIALIZATION
	////////////////////////////////////////////////////////////////////////////

	//serializeResult();

	AVM_OS_LOG << _SEW_ << "< end >Computing ... done." << std::endl;

	return( true );
}


/**
 * SERIALIZATION
 */
void Workflow::toStream(OutStream & os) const
{
	os << TAB << "parameter {" << EOL;

	os << TAB2 << "location = " << mSEWFileLocation << ";"
			<< EOL_INCR_INDENT;

	if( mParameterWObject != WObject::_NULL_ )
	{
		mParameterWObject->toStream(os);
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}

} /* namespace sep */
