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
#include "avm_util.h"

#include "avm_debug.h"
#include "avm_string.h"

#include <printer/OutStream.h>


namespace sep {


/**
 *******************************************************************************
 * AVM EXIT CODE
 *******************************************************************************
 */
AVM_EXIT_CODE_KIND  _AVM_EXIT_CODE_ = AVM_EXIT_GOOD_CODE;


void avm_set_exit_code(AVM_EXIT_CODE_KIND exit_code)
{
	if( _AVM_EXIT_CODE_ == AVM_EXIT_GOOD_CODE )
	{
		_AVM_EXIT_CODE_ = exit_code;
	}
	else if( _AVM_EXIT_CODE_ != exit_code )
	{
AVM_IF_DEBUG_ENABLED

	AVM_OS_WARN << _DBG_ << "Previous exit code: " << std::endl
			<< exit_msg( _AVM_EXIT_CODE_ ) << std::endl;

AVM_ENDIF_DEBUG_ENABLED

		_AVM_EXIT_CODE_ = exit_code;
	}
}


std::string avm_strExitCode(AVM_EXIT_CODE_KIND exit_code)
{

#define CASE_RETURN( code , str )  case AVM_EXIT_##code##_CODE: return( str );

	switch( exit_code )
	{
		CASE_RETURN( GOOD , "good" )

		CASE_RETURN( FAILED , "failed" )


		CASE_RETURN( OUT_OF_MEMORY , "out-of-memory" )

		CASE_RETURN( FATAL_ERROR , "fatal error" )


		CASE_RETURN( CONFIGURE_ERROR , "error in configuration process" )

		CASE_RETURN( PARSING_ERROR , "error in parsing process" )

		CASE_RETURN( PARSING_EXCEPTION , "exception in parsing process" )

		CASE_RETURN( COMPILING_ERROR , "error in compiling process" )


		CASE_RETURN( EXECUTION_ERROR , "error in execution process" )

		CASE_RETURN( RUNTIME_ERROR , "runtime error" )


		CASE_RETURN( INITIALIZING_ERROR , "processor: initialization error" )

		CASE_RETURN( PRE_PROCESSING_ERROR , "processor: pre-processing error" )

		CASE_RETURN( PROCESSING_ERROR , "processor: processing error" )

		CASE_RETURN( POST_PROCESSING_ERROR , "processor: post_processing error" )

		CASE_RETURN( FINALIZING_ERROR , "processor: finalization error" )


		//CONTROLLER UNIT VERDICT
		CASE_RETURN( SYMBEX_CONTROLLER_MIN , "symbex controller: minimal code" )


		CASE_RETURN( COVERAGE_GOAL_ACHIEVED    , "coverage: GOAL ACHIEVED"   )
		CASE_RETURN( COVERAGE_GOAL_UNACHIEVED  , "coverage: GOAL UNACHIEVED" )

		CASE_RETURN( COVERAGE_GOAL_ALMOST_ACHIEVED,	"coverage: ALMOST ACHIEVED")

		CASE_RETURN( COVERAGE_GOAL_UNREACHABLE , "coverage: GOAL UNREACHABLE" )


		CASE_RETURN( VERDICT_PASS                 , "verdict: PASS"        )
		CASE_RETURN( VERDICT_STRONG_PASS          , "verdict: STRONG PASS" )
		CASE_RETURN( VERDICT_WEAK_PASS            , "verdict: WEAK PASS"   )

		CASE_RETURN( VERDICT_INCONCLUSIVE         , "verdict: INCONCLUSIVE")
		CASE_RETURN( VERDICT_INCONCLUSIVE_INPUT   , "verdict: INCONCi"     )
		CASE_RETURN( VERDICT_INCONCLUSIVE_REACTION, "verdict: INCONCr"     )

		CASE_RETURN( VERDICT_NONE                 , "verdict: NONE"        )
		CASE_RETURN( VERDICT_FAIL                 , "verdict: FAIL"        )
		CASE_RETURN( VERDICT_ERROR                , "verdict: ERROR"       )
		CASE_RETURN( VERDICT_ABORT                , "verdict: ABORT"       )

		CASE_RETURN( VERDICT_UNDEFINED            , "verdict: UNDEFINED"   )


		CASE_RETURN( UNKNOWN , "unknown exit code" )

		default: return "undefined exit code";
	}
}


OutStream & operator<<(OutStream & OS, const AvmEXIT_SIGNAL & exitSignal)
{
	return( OS << EMPHASIS( OSS() << "@exit< "
			<< avm_strExitCode( exitSignal.code ) << " > bye !",
			( ((exitSignal.code == AVM_EXIT_GOOD_CODE)
					|| (exitSignal.code > AVM_EXIT_SYMBEX_CONTROLLER_MIN_CODE))
				? '*' : '?' ),
			( ((exitSignal.code == AVM_EXIT_GOOD_CODE)
					|| (exitSignal.code > AVM_EXIT_SYMBEX_CONTROLLER_MIN_CODE))
				? 42 : 80 ) ) << std::flush );

//	return( OS << "@exit< " << avm_strExitCode( exitSignal.code )
//			<< " > bye !" << std::endl );
}


/**
 ***************************************************************************
 * AVM EVAL MODE
 ***************************************************************************
 */
AVM_EXEC_MODE_KIND  _AVM_EXEC_MODE_ = AVM_EXEC_STANDALONE_MODE;

void avm_setExecModeKind(std::string strModeKind)
{
	StringTools::toupper(strModeKind);

	if( strModeKind.empty() )                AVM_EXEC_MODE_SET( STANDALONE     )

	else if( strModeKind == "STANDALONE"  )  AVM_EXEC_MODE_SET( STANDALONE     )

	else if( strModeKind == "SERVER"      )  AVM_EXEC_MODE_SET( SERVER         )

	else if( strModeKind == "GRPC"        )  AVM_EXEC_MODE_SET( SERVER_GRPC    )

	else if( strModeKind == "JSON_RPC"    )  AVM_EXEC_MODE_SET( SERVER_JSON_RPC)

	else if( strModeKind == "INTERACTIVE" )  AVM_EXEC_MODE_SET( INTERACTIVE    )

	else AVM_EXEC_MODE_SET( STANDALONE )
}


std::string  _AVM_EXEC_SERVER_HOST_ADDRESS_ = "localhost";

std::string  _AVM_EXEC_SERVER_PORT_NUMBER_  = "50051";



AVM_EXEC_VERBOSITY_LEVEL  _AVM_EXEC_VERBOSITY_ = AVM_EXEC_VERBOSITY_MAXIMUM;

void avm_setExecVerbosityLevel(std::string strVerbosityLevel)
{
	StringTools::toupper(strVerbosityLevel);

	if( strVerbosityLevel.empty() )           AVM_EXEC_VERBOSITY_SET( MAXIMUM )

	else if( strVerbosityLevel == "SILENT"  ) AVM_EXEC_VERBOSITY_SET( SILENT  )

	else if( strVerbosityLevel == "MINIMUM" ) AVM_EXEC_VERBOSITY_SET( MINIMUM )

	else if( strVerbosityLevel == "MEDIUM"  ) AVM_EXEC_VERBOSITY_SET( MEDIUM  )

	else if( strVerbosityLevel == "MAXIMUM" ) AVM_EXEC_VERBOSITY_SET( MAXIMUM )

	else AVM_EXEC_VERBOSITY_SET( MAXIMUM )
}

std::string avm_strExecVerbosityLevel()
{
	switch( _AVM_EXEC_VERBOSITY_ )
	{
		case AVM_EXEC_VERBOSITY_SILENT : return( "SILENT"  );
		case AVM_EXEC_VERBOSITY_MINIMUM: return( "MINIMUM" );
		case AVM_EXEC_VERBOSITY_MEDIUM : return( "MEDIUM"  );
		case AVM_EXEC_VERBOSITY_MAXIMUM: return( "MAXIMUM" );

		default: return( "VERBOSITY< UNKNOWN >" );
	}
}

///////////////////////////////////////////////////////////////////////////////
// SPIDER VERBOSITY

bool AVM_ENABLED_SPIDER_VERBOSITY_FLAG = false;

void avm_enabledSpiderVerbosity(bool enabled)
{
	AVM_ENABLED_SPIDER_VERBOSITY_FLAG = enabled;
}


}
