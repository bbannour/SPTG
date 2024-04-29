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

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

#include <server/grpc/SymbexServer.h>

#endif /* _EXPERIMENTAL_SERVER_GRPC_FEATURE_ */

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>

#include <util/avm_vfs.h>
#include <util/ExecutionTime.h>

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

#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )
			else if( arg == "--enable-server-grpc-mode" )
			{
				AVM_EXEC_MODE_SET( SERVER_GRPC );
			}
			else if( arg.find("--host=") == 0 )
			{
				_AVM_EXEC_SERVER_HOST_ADDRESS_ =
					arg.substr(std::strlen("--host="), arg.size());
			}

			else if( arg.find("--port=") == 0 )
			{
				std::string strPortNumber =
					arg.substr(std::strlen("--port="), arg.size());

				try
				{
					if( std::stol(strPortNumber.c_str()) > 0)
					{
						_AVM_EXEC_SERVER_PORT_NUMBER_ = strPortNumber;
					}
					else
					{
						std::cerr << "Unexpected negative port number< " << strPortNumber
								<< " > as argument !"<< std::endl;
					}
				}
				catch (std::invalid_argument & invalid_arg)
				{
					std::cerr << "Invalid port number< " << strPortNumber
							<< " > as argument !" << std::endl;
				}
				catch (std::out_of_range & oor)
				{
					std::cerr << "Out of range port number< " << strPortNumber
							<< " > as argument !" << std::endl;
				}
				catch (std::exception  & e)
				{
					std::cerr << "Unexpected port number< " << strPortNumber
							<< " > as argument ! --> exception : "
							<< e.what() << std::endl;
				}
			}
			else if( arg == "--port" )
			{
				std::string strPortNumber = getArgument( ++i );

				try
				{
					if( std::stol(strPortNumber.c_str()) > 0)
					{
						_AVM_EXEC_SERVER_PORT_NUMBER_ = strPortNumber;
					}
					else
					{
						std::cerr << "Unexpected negative port number< " << strPortNumber
								<< " > as argument !"<< std::endl;
					}
				}
				catch (std::invalid_argument & invalid_arg)
				{
					std::cerr << "Invalid port number< " << strPortNumber
							<< " > as argument !" << std::endl;
				}
				catch (std::out_of_range & oor)
				{
					std::cerr << "Out of range port number< " << strPortNumber
							<< " > as argument !" << std::endl;
				}
				catch (std::exception  & e)
				{
					std::cerr << "Unexpected port number< " << strPortNumber
							<< " > as argument ! --> exception : "
							<< e.what() << std::endl;
				}
			}
#endif // _EXPERIMENTAL_SERVER_GRPC_FEATURE_

#if defined( EXPERIMENTAL_FEATURE )
			else if( arg == "--enable-server-json_rpc-mode" )
			{
				AVM_EXEC_MODE_SET( SERVER_JSON_RPC );
			}
#endif // EXPERIMENTAL_FEATURE

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
					|| (arg == "--print-enabled-fam-list") )
			{
				ProcessorUnitRepository::toStreamAll( AVM_OS_COUT );

				FamExposer::toStreamExported( AVM_OS_COUT );
			}
			else if( arg == "--print-enabled-solvers-list" )
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
	AVM_OS_COUT << std::endl << AVM_TAB1_INDENT
			<< TAB << "SYMBEX< DIVERSITY > "

#ifndef _AVM_BUILT_WITH_CMAKE_

			<< SYMBEX_BUILD_INFO
#else
			<< sources_commit_id << " built on " << system_name

#endif /*_BUILT_WITH_CMAKE_*/

			<< " @ " << __DATE__ << std::endl
			<< TAB << "2024 CEA List" << std::endl
//			<< TAB << "2010 - 2019 CEA List" << std::endl
//			<< TAB << "1998 - 2013 CEA List" << std::endl
			<< TAB << "All Rights Reserved" << std::endl
			<< TAB << "Launch @ " << ExecutionTime::current_time()
			<< std::endl << END_INDENT;
}


/**
 * AvmLauncher::usage
 *
 */
void AvmLauncher::help()
{
	AVM_OS_COUT << "Usage : ${DIVERSITY_EXEC} [options] [workflow-params-file]"
		<< std::endl
		<< "Workflow : a file that specifies the type of formal analysis"
			"\n           to be performed via a list of parameters"
			"\n           (as \"key-value pairs\" representation) for"
			"\n           xLIA model file, module analysis configuration,"
			"\n           stop criterion, reporting options ..."
		<< std::endl
		<< "Options :"
		<< std::endl
		<< TAB2 << "--print-enabled-fam-list , --print-enabled-processors-list" << std::endl
		<< TAB4 << "print the list of enabled FAM, Formal Analysis Modules"
		<< std::endl
		<< TAB2 << "--print-enabled-solvers-list" << std::endl
		<< TAB4 << "print the list of available SMT-Solvers" << std::endl
#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )
		<< TAB2 << "--enable-server-grpc-mode [--port=number]" << std::endl
		<< TAB4 << "execute DIVERSITY using the gRPC server mode on 'localhost:port' with default port 50051" << std::endl
#endif // _EXPERIMENTAL_SERVER_GRPC_FEATURE_
		<< std::endl;
}

void AvmLauncher::usage()
{
	AVM_OS_COUT << "Usage : DIVERSITY_EXEC [options] [workflow-params-file]"
		<< std::endl
		<< "try DIVERSITY_EXEC --help" << std::endl;

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
#if defined( _EXPERIMENTAL_SERVER_GRPC_FEATURE_ )

					grpc::SymbexServer::runServer();

#endif // _EXPERIMENTAL_SERVER_GRPC_FEATURE_

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

	AVM_OS_COUT << exit_msg( _AVM_EXIT_CODE_ );


	return( _AVM_EXIT_CODE_ );
}


} /* namespace sep */
