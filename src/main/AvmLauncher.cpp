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

#include <filesystem>

#include <base/ClassKindInfo.h>

#include <builder/Builder.h>

#include <main/FamExposer.h>
#include <main/SignalHandler.h>
#include <main/StaticInitializer.h>

#include <computer/EnvironmentFactory.h>

#include <famcore/api/ProcessorUnitRepository.h>

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/ExpressionFactory.h>

#include <fml/lib/AvmLang.h>

#include <fml/runtime/RuntimeLib.h>

#include <fml/type/TypeManager.h>

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>

#include <util/avm_vfs.h>
#include <util/ExecutionTime.h>

namespace sep
{

std::string AvmLauncher::SYMBEX_BUILD_ID = "4.0";

/**
 * LOADER
 */
bool AvmLauncher::load()
{
	copyright();

	if( getArgNumber() > 1 )
	{
		StaticInitializer::load();

		std::string arg;
		for( std::size_t i = 1 ; i < getArgNumber() ; ++i )
		{
			arg = getArgument( i );

			if( arg[0] != '-' )
			{
				VFS::WorkflowPath = arg;
			}
			else if( arg.find("--sew=") == 0 )
			{
				VFS::WorkflowPath =
						arg.substr(std::strlen("--sew="), arg.size());
			}
			else if( (arg.find("--favm=") == 0) || (arg.find("--spec=") == 0) )
			{
				VFS::WorkflowPath =
						arg.substr(std::strlen("--favm="), arg.size());
			}
			else if( (arg == "--sew") || (arg == "--favm") || (arg == "--spec") )
			{
				VFS::WorkflowPath = getArgument( ++i );
			}

			else if( arg == "--enable-standalone-mode" )
			{
				AVM_EXEC_MODE_SET( STANDALONE );
			}
			else if( arg == "--enable-server-mode" )
			{
				AVM_EXEC_MODE_SET( SERVER );
			}

			else if( arg == "--enable-interactive-mode" )
			{
				AVM_EXEC_MODE_SET( INTERACTIVE );
			}

			else if( arg.find("--log-output-file=") == 0 )
			{
				AVM_LOG_FILE_LOCATION =
					arg.substr(std::strlen("--log-output-file="), arg.size());
			}
			else if( arg == "--log-output-file" )
			{
				AVM_LOG_FILE_LOCATION = getArgument( ++i );
			}

			else if( arg.find("--trace-output-file=") == 0 )
			{
				AVM_TRACE_FILE_LOCATION =
					arg.substr(std::strlen("--trace-output-file="), arg.size());
			}
			else if( arg == "--trace-output-file" )
			{
				AVM_TRACE_FILE_LOCATION = getArgument( ++i );
			}

			else if( arg.find("--debug-options=") == 0 )
			{
				avm_setDebugLevel(
					arg.substr(std::strlen("--debug-options="), arg.size()) );
			}
			else if( arg == "--debug-options" )
			{
				avm_setDebugLevel( getArgument( ++i ) );
			}

			else if( arg == "--verbosity-silent" )
			{
				AVM_EXEC_VERBOSITY_SET( SILENT );
			}
			else if( arg == "--verbosity-minimum" )
			{
				AVM_EXEC_VERBOSITY_SET( MINIMUM );
			}
			else if( arg == "--verbosity-medium" )
			{
				AVM_EXEC_VERBOSITY_SET( MEDIUM );
			}
			else if( arg == "--verbosity-maximum" )
			{
				AVM_EXEC_VERBOSITY_SET( MAXIMUM );
			}

			else if( arg.find("--verbosity-level=") == 0 )
			{
				avm_setExecVerbosityLevel(
					arg.substr(std::strlen("--verbosity-level="), arg.size()) );
			}
			else if( arg == "--verbosity-level" )
			{
				avm_setExecVerbosityLevel( getArgument( ++i ) );
			}

			else if( arg == "--enable-print-spider-positions" )
			{
				avm_enabledSpiderVerbosity( true );
			}

			else if( (arg == "--print-enabled-processors-list")
					|| (arg == "--print-enabled-fam-list")
					|| (arg == "-fam")
					|| (arg == "--formal_analysis_modules") )
			{
				ProcessorUnitRepository::toStreamAll( AVM_OS_COUT );

				FamExposer::toStreamExported( AVM_OS_COUT );
			}
			else if( (arg == "--print-enabled-solvers-list")
					|| (arg == "-smt")
					|| (arg == "--smt_solvers") )
			{
				SolverDef::toStreamSolverList( AVM_OS_COUT );
			}

			else if( (arg == "--help") || (arg == "-help") || (arg == "-h") )
			{
				help();
			}

			else
			{
				AVM_OS_WARNING_ALERT
						<< "Unknown AVM launch option << " << arg << " >> !!!"
						<< SEND_ALERT;
			}
		}

		mWorkflow.load();

		reportInstanceCounterUsage(AVM_OS_LOG, "AvmLauncher::load at the end");

		return( true );
	}
	else
	{
		usage();

		return( false );

	}
}


/**
 * DISPOSER
 */
void AvmLauncher::dispose()
{
	mWorkflow.dispose();

	StaticInitializer::dispose();

	copyright();
}


void AvmLauncher::copyright()
{
	AVM_OS_COUT << std::endl
//			<< TAB << "SYMBEX< DIVERSITY > "
			<< TAB << "SYMBEX< SPTG > "

#ifndef _AVM_BUILT_WITH_CMAKE_

//			<< SYMBEX_BUILD_INFO
#else
			<< sources_commit_id << " built on " << system_name

#endif /*_BUILT_WITH_CMAKE_*/

			<< std::endl
			<< TAB << "2025 CEA List" << std::endl
			<< TAB << "All Rights Reserved" << std::endl
			<< TAB << "Launch @ " << ExecutionTime::current_time()
			<< std::endl ;
}


/**
 * AvmLauncher::usage
 *
 */
static const std::string HELP = R""""(
Usage: sptg.exe [OPTIONS] [Symbolic_Execution_Workflow_file.sew]

Options:
  -fam, --formal_analysis_module  Print all available Formal Analysis Modules
  -smt, --smt_solver              Print all usable Satisfiability Modulo Theories (SMT) solvers
  -h  , --help                    Print help
)"""";
void AvmLauncher::help()
{
	AVM_OS_COUT << HELP << std::endl;
}

void AvmLauncher::usage()
{
	AVM_OS_COUT << "Usage : sptg.exe [OPTIONS] [Symbolic_Execution_Workflow_file.sew]"
		<< std::endl
		<< "try sptg.exe --help" << std::endl;

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
	 * Loading  Workflow Parameter
	 */
	if( not mWorkflowParameter.loadConfiguration(VFS::WorkflowPath) )
	{
		return;
	}

	/*
	 * RUNNING
	 * parameter
	 */
	try
	{
		SignalHandler::setSIGINT_handler();

		if( mWorkflow.configure(mWorkflowParameter) )
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
	if( argv != nullptr )
	{
		VFS::ExecutablePath = argv[0];
	}
	VFS::LaunchPath = std::filesystem::current_path().string();

	std::string strAction = " The AvmLauncher::main";

	try
	{
		sep::AvmLauncher theAvmLauncher(
				(argc < 0)? 0 : static_cast< std::size_t >(argc) , argv);

		strAction = " The AvmLauncher::load";
		if( theAvmLauncher.load() )
		{
			switch( _AVM_EXEC_MODE_ )
			{
				case  AVM_EXEC_SERVER_GRPC_MODE:
				case  AVM_EXEC_SERVER_JSON_RPC_MODE:
				{
					break;
				}
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

							reportInstanceCounterUsage(AVM_OS_LOG,
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

	AVM_OS_COUT << exit_msg( _AVM_EXIT_CODE_ ) << std::flush;

	return( _AVM_EXIT_CODE_ );
}


} /* namespace sep */
