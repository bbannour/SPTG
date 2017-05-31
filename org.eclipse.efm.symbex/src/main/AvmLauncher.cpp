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

#include "AvmLauncher.h"

#include <base/ClassKindInfo.h>

#include <builder/Builder.h>
#include <builder/Loader.h>

#include <main/SignalHandler.h>

#include <computer/EnvironmentFactory.h>

#include <fam/api/ProcessorUnitRepository.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/ExpressionFactory.h>

#include <fml/runtime/RuntimeLib.h>

#include <fml/type/TypeManager.h>

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>

#include <util/avm_string.h>
#include <util/ExecutionTime.h>

#include <boost/filesystem.hpp>

#ifdef _AVM_BUILT_WITH_CMAKE_
#include "version.h"
#include "confs.h"
#endif /*_AVM_BUILT_WITH_CMAKE_*/


namespace sep
{

#define _SYMBEX_VERSION_            3
#define _SYMBEX_VERSION_MAJOR_      6
#define _SYMBEX_VERSION_PATCHLEVEL_ 0


//const unsigned    AvmLauncher::SUBVERSION_REVISION_NUMBER = 4838;
//const std::string AvmLauncher::SUBVERSION_REVISION_STRING = "4838";


#ifdef _GIT_VERSION_

	#define GIT_VERSION   _GIT_VERSION_

#else

//	#define GIT_VERSION "\"$(shell git describe --always --tags)\""
	#define GIT_VERSION "\"$(shell git rev-parse HEAD)\""

#endif


std::string AvmLauncher::SYMBEX_SCM_VERSION = GIT_VERSION;
//		OSS("") << _SYMBEX_VERSION_ << '.' << _SYMBEX_VERSION_MAJOR_;
////			<< '.' << _SYMBEX_VERSION_PATCHLEVEL_;

std::string AvmLauncher::SYMBEX_BUILD_ID = GIT_VERSION;
//		SUBVERSION_REVISION_STRING;

std::string AvmLauncher::SYMBEX_BUILD_INFO =
		OSS("") << "Git-Version< " << SYMBEX_SCM_VERSION << " >";
//		OSS("") << "Version " << SYMBEX_SCM_VERSION
//				<< " build " << SYMBEX_BUILD_ID;


/**
 * LOADER
 */
bool AvmLauncher::load()
{
	copyright();

	if( getArgNumber() > 1 )
	{
		std::string arg;
		for( avm_size_t i = 1 ; i < getArgNumber() ; ++i )
		{
			arg = getArgument( i );

			if( arg[0] != '-' )
			{
				VFS::WorkflowPath = arg;
			}
			else if( (arg.find("--favm=") == 0) || (arg.find("--spec=") == 0) )
			{
				VFS::WorkflowPath =
						arg.substr(std::strlen("--favm="), arg.size());
			}
			else if( (arg == "--favm") || (arg == "--spec") )
			{
				VFS::WorkflowPath = getArgument( ++i );
			}

			else if( arg == "--standalone" )
			{
				AVM_EXEC_MODE_SET( STANDALONE );
			}
			else if( (arg == "--server") || (arg == "-server") )
			{
				AVM_EXEC_MODE_SET( SERVER );
			}
			else if( arg == "--interactive" )
			{
				AVM_EXEC_MODE_SET( INTERACTIVE );
			}

			else if( arg.find("--log=") == 0 )
			{
				AVM_LOG_FILE_LOCATION =
						arg.substr(std::strlen("--log="), arg.size());
			}
			else if( arg == "--log" )
			{
				AVM_LOG_FILE_LOCATION = getArgument( ++i );
			}

			else if( arg.find("--trace=") == 0 )
			{
				AVM_LOG_FILE_LOCATION =
						arg.substr(std::strlen("--trace="), arg.size());
			}
			else if( arg == "--trace" )
			{
				AVM_TRACE_FILE_LOCATION = getArgument( ++i );
			}

			else if( arg.find("--debug=") == 0 )
			{
				avm_setDebugLevel(
						arg.substr(std::strlen("--debug="), arg.size()) );
			}
			else if( arg == "--debug" )
			{
				avm_setDebugLevel( getArgument( ++i ) );
			}

			else if( arg == "--silent" )
			{
				AVM_EXEC_VERBOSITY_SET( MINIMUM );
			}

			else if( arg.find("--verbosity=") == 0 )
			{
				avm_setExecVerbosityLevel(
						arg.substr(std::strlen("--verbosity="), arg.size()) );
			}
			else if( arg == "--verbosity" )
			{
				avm_setExecVerbosityLevel( getArgument( ++i ) );
			}

			else if( (arg == "--enabled-processors-list")
					|| (arg == "--enabled-fam-list") )
			{
				ProcessorUnitRepository::toStreamAll( AVM_OS_COUT );

				ProcessorUnitRepository::toStreamExported( AVM_OS_COUT );
			}
			else if( arg == "--enabled-solvers-list" )
			{
				SolverDef::toStreamSolverList( AVM_OS_COUT );
			}

			else
			{
				AVM_OS_WARNING_ALERT
						<< "Unknown AVM launch option << " << arg << " >> !!!"
						<< SEND_ALERT;
			}
		}
	}
	else
	{
		usage();

		::exit(1);
	}

	/*
	 * LOAD
	 * Predefined FORM
	 */
	XLIA_SYNTAX::load();

	ExpressionFactory::load();

	// after loading parameter...
	//	SolverFactory::load();

	TypeManager::load();


	EnvironmentFactory::load();

	Builder::load();

	ExecutableLib::load();

	RuntimeLib::load();


	mWorkflow.load();

	avm_report(AVM_OS_LOG, "AvmLauncher::load at the end");

	return( true );
}


/**
 * DISPOSER
 */
void AvmLauncher::dispose()
{
	EnvironmentFactory::dispose();

	SolverFactory::dispose();


	mWorkflow.dispose();


	RuntimeLib::dispose();

	ExecutableLib::dispose();

	Builder::dispose();


	TypeManager::dispose();

	ExpressionFactory::dispose();

	XLIA_SYNTAX::dispose();

	copyright();
}


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
void AvmLauncher::copyright()
{
	AVM_OS_COUT << std::endl << AVM_TAB1_INDENT
			<< TAB << "SYMBEX< DIVERSITY > "

#ifndef _AVM_BUILT_WITH_CMAKE_

			<< SYMBEX_BUILD_INFO
#else
			<< sources_commit_id << " built on " << system_name

#endif /*_BUILT_WITH_CMAKE_*/

			<< " @ " << __DATE__ << std::endl
			<< TAB << "2010 - 2016 CEA List" << std::endl
//			<< TAB << "1998 - 2013 CEA List" << std::endl
			<< TAB << "All Rights Reserved" << std::endl
			<< TAB << "Launch @ " << ExecutionTime::current_time()
			<< std::endl << END_INDENT;
}


/**
 * AvmLauncher::usage
 *
 */
void AvmLauncher::usage()
{
	AVM_OS_LOG << " Usage :> avm.exe parameterfile (in FAVM format)" << std::endl;

	std::cin.get();
}


/**
 * AvmLauncher::start
 *
 */
void AvmLauncher::start()
{
	/*
	 * INITIALIZATION
	 * parameter FORM
	 */
	if( not mWorkflow.loadConfiguration(VFS::WorkflowPath) )
	{
		return;
	}

	SolverFactory::load();

	/*
	 * RUNNING
	 * parameter FORM
	 */
	try
	{
		SignalHandler::setSIGINT_handler();

		if( mWorkflow.configure() )
		{
			mWorkflow.startComputing();
		}
	}
	catch ( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"AvmLauncher::start< std::exception >", e.what(), '*', 80);
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"AvmLauncher::start< unknown::exception > !!!", '*', 80);
	}
}


int AvmLauncher::run( int argc , char * argv[] )
{
	if( argv != NULL )
	{
		VFS::ExecutablePath = argv[0];
	}
	VFS::LaunchPath = boost::filesystem::current_path().string();

	ClassKindInfoInitializer::load();

	std::string strAction = " The AvmLauncher::main";

	OutStream::load();

	try
	{
		sep::AvmLauncher theAvmLauncher(
				(argc < 0)? 0 : static_cast< avm_size_t >(argc) , argv);

		strAction = " The AvmLauncher::load";
		if( theAvmLauncher.load() )
		{
			switch( _AVM_EXEC_MODE_ )
			{
				case AVM_EXEC_STANDALONE_MODE:
				case AVM_EXEC_SERVER_MODE:
				case AVM_EXEC_INTERACTIVE_MODE:
				default:
				{
					if( not VFS::WorkflowPath.empty() )
					{
						VFS::WorkflowPath = VFS::native_path(
								VFS::WorkflowPath, VFS::LaunchPath);

						if( VFS::checkReadingFile( VFS::WorkflowPath ) )
						{
							strAction = " TheAvmLauncher::start";

							theAvmLauncher.start();

							avm_report(AVM_OS_LOG,
									"AvmLauncher::run after this.start()");
						}
						else
						{
							AVM_OS_CERR << _SEW_ << "< error >"
									" Unreadable or non-existent file !"
									<< std::endl
									<< _SEW_ << "< info  > Launch path : "
									<< VFS::LaunchPath << std::endl;

							avm_set_exit_code( AVM_EXIT_CONFIGURE_ERROR_CODE );
						}
					}
					break;
				}
			}
		}

		strAction = " The AvmLauncher::dispose";

		theAvmLauncher.dispose();
	}
	catch ( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			(strAction + "< std::exception > "), e.what(), '*', 80);
	}
	catch ( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			(strAction + "< unknown::exception > !!!"), '*', 80);
	}


	avm_report(AVM_OS_LOG, "::main at the end");

AVM_IF_DEBUG_FLAG( REFERENCE_COUNTING )

	avm_report(AVM_OS_COUT, "::main at the end");

AVM_ENDIF_DEBUG_FLAG( REFERENCE_COUNTING )


	OutStream::dispose();

	ClassKindInfoInitializer::dispose();

	AVM_OS_COUT << exit_msg( _AVM_EXIT_CODE_ );

	return( _AVM_EXIT_CODE_ );
}


} /* namespace sep */
