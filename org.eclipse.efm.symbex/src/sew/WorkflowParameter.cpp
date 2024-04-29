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

#include "WorkflowParameter.h"

#include <fstream>
#include <list>
#include <string>

#include <builder/primitive/CompilationEnvironment.h>

#include <collection/List.h>
#include <collection/Typedef.h>

#include <fml/infrastructure/PropertyPart.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeID.h>

#include <parser/ParserManager.h>

#include <printer/Manipulators.h>
#include <printer/OutStream.h>

#include <sew/Configuration.h>
#include <sew/SymbexEngine.h>

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>

#include <util/avm_debug.h>
#include <util/avm_util.h>


namespace sep
{


/**
 * GLOBALS
 */
const std::string & WorkflowParameter::SECTION_WORKSPACE_REGEX_ID =
		OR_WID3( "workspace" , "WORKSPACE" , "LOCATION" );

const std::string & WorkflowParameter::SECTION_CONSOLE_REGEX_ID =
		OR_WID3( "console" , "CONSOLE" , "AVM" );

const std::string & WorkflowParameter::SECTION_DEVELOPER_REGEX_ID =
		OR_WID3( "developer" , "DEVELOPER" , "TRACE");

const std::string & WorkflowParameter::SECTION_DIRECTOR_REGEX_ID =
		OR_WID4( "director" , "DIRECTOR" , "MOC" , "RUNTIME");

const std::string & WorkflowParameter::SECTION_SHELL_REGEX_ID =
		OR_WID3( "shell" , "SHELL" , "AVM");

const std::string & WorkflowParameter::SECTION_SYMBEX_REGEX_ID =
		OR_WID3( "symbex" , "SYMBEX" , "AVM");

const std::string & WorkflowParameter::SECTION_TDD_REGEX_ID =
		OR_WID2( "tdd" , "TDD");


const std::string & WorkflowParameter::SECTION_FAM_REGEX_ID =
		OR_WID2(OR_WID4( "controller" , "worker" , "processor" , "filter" ),
				OR_WID4( "CONTROLLER" , "WORKER" , "PROCESSOR" , "FILTER" ));


const std::string & WorkflowParameter::SECTION_FAM_CONTAINERS_REGEX_ID =
		OR_WID4(OR_WID4( "controller" , "worker" , "processor" , "filter" ),
				OR_WID4( "CONTROLLER" , "WORKER" , "PROCESSOR" , "FILTER" ),
				OR_WID3( "queue" , "pre_process" , "post_process" ),
				OR_WID3( "QUEUE" , "PRE_PROCESS" , "POST_PROCESS" ));

// Deprecated
const std::string & WorkflowParameter::SECTION_FAM_QUEUE_REGEX_ID =
		OR_WID2( "queue" , "QUEUE" );

const std::string & WorkflowParameter::SECTION_FAM_REDUNDANCY_REGEX_ID =
		OR_WID2( "redundancy" , "REDUNDANCY" );

const std::string & WorkflowParameter::SECTION_FAM_PROCESSOR_REGEX_ID =
		OR_WID2(OR_WID3( "controller" , "worker" , "processor" ),
				OR_WID3( "CONTROLLER" , "WORKER" , "PROCESSOR" ));

const std::string & WorkflowParameter::SECTION_FAM_FILTER_REGEX_ID =
		OR_WID2( "filter" , "FILTER" );

const std::string & WorkflowParameter::SECTION_FAM_PREPROCESS_REGEX_ID =
		OR_WID2( "pre_process" , "PRE_PROCESS" );

const std::string & WorkflowParameter::SECTION_FAM_POSTPROCESS_REGEX_ID =
		OR_WID2( "post_process" , "POST_PROCESS" );


/**
 * SINGLETON
 */
WorkflowParameter * WorkflowParameter::INSTANCE = nullptr;


////////////////////////////////////////////////////////////////////////////////
///// AVM CONFIGURATION PARAMETER CHECKER
////////////////////////////////////////////////////////////////////////////////

bool WorkflowParameter::loadConfiguration(const std::string & aWorkflowLocation)
{
	mSEWFileLocation = aWorkflowLocation;

	// Checking WORKFLOW
	AVM_OS_COUT << _SEW_
			<< "Symbolic Execution based WorkflowParameter analysis ... START"
			<< std::endl;

	AVM_OS_COUT << _SEW_ << "Location: " << VFS::parent( mSEWFileLocation )
			<< std::endl;

	// Load workflow definition file
	AVM_OS_COUT << _SEW_ << "WorkflowParameter: " << VFS::filename( mSEWFileLocation )
			<< std::endl;

	std::ifstream fileStream( mSEWFileLocation );

	return( loadConfiguration(fileStream) );
}


bool WorkflowParameter::loadConfiguration(
		const std::string & rawWorkflowParameters,
		const std::string & aWorkflowLocation)
{
	mSEWFileLocation = aWorkflowLocation;

	std::istringstream strStream( rawWorkflowParameters );

	return( loadConfiguration(strStream) );
}


bool WorkflowParameter::loadConfiguration(std::istream & anInputStream)
{
	if( not parseConfiguration(anInputStream) )
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
	isOK = OutStream::configure(*this)
		&& isOK;

AVM_IF_DEBUG_LEVEL_FLAG2_AND(HIGH , PARSING , CONFIGURING ,
		(mParameterWObject != WObject::_NULL_) )

	std::string parseResultFile = VFS::suffixFilename(
			VFS::filename( mSEWFileLocation ), "_parsed", ".sew");

	parseResultFile = VFS::native_path(parseResultFile,
			VFS::WorkspaceDebugPath.empty()
					? VFS::parent( mSEWFileLocation )
					: VFS::WorkspaceDebugPath );

	OS_INIT_LOG << _DBG_
			<< "Saving of the parsed WorkflowParameter in text format ..."
			<< std::endl;

	Configuration::saveElementTextualView(
			OS_INIT_LOG, mParameterWObject, parseResultFile);

AVM_ENDIF_DEBUG_LEVEL_FLAG2_AND(HIGH , PARSING , CONFIGURING )

	if( isOK )
	{
		AVM_OS_LOG << _SEW_ << "Symbolic Execution "
				"based WorkflowParameter analysis ... START"
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

	if( isOK )
	{
		reportInstanceCounterUsage(OS_INIT_LOG, "WorkflowParameter::loadConfiguration:> "
				"end of avm configuration checking !!!");
	}
	else
	{
		avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );
	}

	AVM_OS_CLOG << _SEW_
			<< "Symbolic Execution based WorkflowParameter analysis ... "
			<< ( isOK ? "DONE" : "FAILED !" )
			<< std::endl << std::endl;

	return( isOK );
}


/**
 * Load workflow definition file
 */
bool WorkflowParameter::parseConfiguration(std::istream & anInputStream)
{
	if( anInputStream.good() )
	{
		ParserManager aParser( mSEWFileLocation );

		mParameterWObject = aParser.parseSEW(mWObjectManager, anInputStream);

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
bool WorkflowParameter::loadCoreElementsConfig(OutStream & LOGGER)
{
	// Set console verbosity level
	const WObject * configCONSOLE = Query::getRegexWSequence(
			mParameterWObject, WorkflowParameter::SECTION_CONSOLE_REGEX_ID);

	avm_setExecVerbosityLevel(
			Query::getRegexWPropertyString(
					configCONSOLE, "verbos(ity|e)", "MAXIMUM") );

	// DEVELOPER
	const WObject * configDEVELOPER = getDEVELOPER();

	// Set developer debug level
	avm_setDebugLevel(
			Query::getWPropertyString(configDEVELOPER, "level", "ZERO") );

	// Set developer debug flags
	ListOfString listOfFlags;
	Query::getRegexWPropertyString(
			configDEVELOPER, OR_WID2("flag", "kind"), listOfFlags);

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
bool WorkflowParameter::loadWorkspaceLocationsConfig(OutStream & LOGGER)
{
	bool isOK = true;

	/*
	 * CHECKING FILE AND FOLDER
	 */
	LOGGER << _SEW_ << "The launch! folder: "
			<< VFS::LaunchPath << std::endl;

	const WObject * configWORKSPACE = Query::getRegexWSequence(
			mParameterWObject, WorkflowParameter::SECTION_WORKSPACE_REGEX_ID);

	std::string relativeLaunchPath = VFS::native_path(
			Query::getWPropertyString(configWORKSPACE, "launch", "."),
			VFS::LaunchPath);

	LOGGER << _SEW_ << "The working folder: "
			<< VFS::relativelaunchPath( relativeLaunchPath ) << std::endl;

	VFS::ProjectPath = VFS::WorkspaceRootPath = VFS::native_path(
			Query::getRegexWPropertyString(
				configWORKSPACE, OR_WID2("root", "project"), relativeLaunchPath),
			VFS::LaunchPath);

	if( (not VFS::checkReadingFolder(VFS::WorkspaceRootPath))
		&& (VFS::WorkspaceRootPath != relativeLaunchPath)
		&& VFS::checkReadingFolder(relativeLaunchPath) )
	{
		VFS::ProjectPath = VFS::WorkspaceRootPath = relativeLaunchPath;
	}

	LOGGER << _SEW_ << "The <wroot> folder: "
			<< VFS::WorkspaceRootPath << std::endl;

	if( VFS::checkReadingFolder(VFS::WorkspaceRootPath) )
	{
		VFS::ProjectSourcePath = VFS::WorkspaceSourcePath =
				VFS::native_path(
						Query::getRegexWPropertyString(
							configWORKSPACE, OR_WID2("source", "src"), "."),
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
						Query::getRegexWPropertyString(
							configWORKSPACE, OR_WID2("output", "out"), "output"),
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
					Query::getRegexWPropertyString(
						configWORKSPACE, OR_WID2("debug", "dbg"), "debug"),
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


	const WObject * configTDD =
			Query::getRegexWSequence(mParameterWObject, SECTION_TDD_REGEX_ID);
		if( Query::hasWPropertyString(configTDD, "report") )
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
				<< "< error > The <wroot> (nor relative <launch>) "
				"folder location ==> doesn't exist or is not Readable !!!"
				<< std::endl << std::endl;

		isOK = false;
	}

	return( isOK );
}


/**
 * Prologue options
 */
void WorkflowParameter::setPrologueOption(
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
			String::_EMPTY_.to< String >().setQuoteChar(
					String::DEFAULT_DELIMITER = value.toCharacter() );
		}
		else if( value.isBuiltinString() )
		{
			std::string delim = value.toBuiltinString();

			String::_EMPTY_.to< String >().setQuoteChar(
					String::DEFAULT_DELIMITER =
							( delim.empty() ? '\0' : delim[0] ) );
		}
	}
}


const WObject * WorkflowParameter::getEngineWObject() const {

	const WObject * sequenceDIRECTOR = getDIRECTOR();
	List< WObject * > engineList;
	Query::getListWObject(sequenceDIRECTOR, engineList);
	if (engineList.nonempty()) {
		return engineList.first();
	}
	else {
		return WObject::_NULL_;
	}

}

/**
 * SERIALIZATION
 */
void WorkflowParameter::toStream(OutStream & os) const
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
