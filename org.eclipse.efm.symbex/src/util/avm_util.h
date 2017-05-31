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
#ifndef AVM_UTIL_H_
#define AVM_UTIL_H_

#include <iostream>
#include <string>


namespace sep {


class OutStream;



/**
 *******************************************************************************
 * AVM EXIT CODE
 *******************************************************************************
 */

enum AVM_EXIT_CODE_KIND
{
	AVM_EXIT_GOOD_CODE                      = 0,

	AVM_EXIT_FAILED_CODE                    = 1,

	AVM_EXIT_OUT_OF_MEMORY_CODE             = 2,

	AVM_EXIT_SEGMENTATION_FAULT_CODE        = 3,

	AVM_EXIT_FATAL_ERROR_CODE               = 4,


	AVM_EXIT_CONFIGURE_ERROR_CODE           = 5,


	AVM_EXIT_PARSING_ERROR_CODE             = 6,

	AVM_EXIT_PARSING_EXCEPTION_CODE         = 7,

	AVM_EXIT_COMPILING_ERROR_CODE           = 8,


	AVM_EXIT_EXECUTION_ERROR_CODE           = 9,

	AVM_EXIT_RUNTIME_ERROR_CODE             = 10,


	AVM_EXIT_INITIALIZING_ERROR_CODE        = 11,

	AVM_EXIT_PRE_PROCESSING_ERROR_CODE      = 12,

	AVM_EXIT_PROCESSING_ERROR_CODE          = 13,

	AVM_EXIT_POST_PROCESSING_ERROR_CODE     = 14,

	AVM_EXIT_FINALIZING_ERROR_CODE          = 15,


	//CONTROLLER UNIT VERDICT
	AVM_EXIT_SYMBEX_CONTROLLER_MIN_CODE     = 100,


	AVM_EXIT_COVERAGE_GOAL_ACHIEVED_CODE    = 101,

	AVM_EXIT_COVERAGE_GOAL_UNACHIEVED_CODE  = 102,

	AVM_EXIT_COVERAGE_GOAL_ALMOST_ACHIEVED_CODE = 103,

	AVM_EXIT_COVERAGE_GOAL_UNREACHABLE_CODE = 104,


	AVM_EXIT_VERDICT_PASS_CODE              = 110,

	AVM_EXIT_VERDICT_STRONG_PASS_CODE       = 111,

	AVM_EXIT_VERDICT_WEAK_PASS_CODE         = 112,


	AVM_EXIT_VERDICT_INCONCLUIVE_CODE       = 113,

	AVM_EXIT_VERDICT_INCONCLUIVE_INPUT_CODE = 114,

	AVM_EXIT_VERDICT_INCONCLUIVE_R_CODE     = 115,


	AVM_EXIT_VERDICT_NONE_CODE              = 116,

	AVM_EXIT_VERDICT_FAIL_CODE              = 117,

	AVM_EXIT_VERDICT_ERROR_CODE             = 118,

	AVM_EXIT_VERDICT_ABORT_CODE             = 119,

	AVM_EXIT_VERDICT_UNDEFINED_CODE         = 120,


	AVM_EXIT_UNKNOWN_CODE                   = 255
};

extern AVM_EXIT_CODE_KIND  _AVM_EXIT_CODE_;

void avm_set_exit_code(AVM_EXIT_CODE_KIND exit_code);

std::string avm_strExitCode(AVM_EXIT_CODE_KIND exit_code);


/**
 * MANIPULATORS
 * for operator<<
 */
class OutStream;

struct AvmEXIT_SIGNAL
{
	friend OutStream & operator<<(OutStream & OS,
			const AvmEXIT_SIGNAL & exitSignal);


	AVM_EXIT_CODE_KIND code;

	AvmEXIT_SIGNAL(AVM_EXIT_CODE_KIND eck)
	: code( eck )
	{
		//!! NOTHING
	}
};

inline AvmEXIT_SIGNAL exit_signal(AVM_EXIT_CODE_KIND code)
{
	return( code );
}

inline AvmEXIT_SIGNAL exit_msg(AVM_EXIT_CODE_KIND code)
{
	return( code );
}


/**
 * operator<<
 */
OutStream & operator<<(OutStream & OS, const AvmEXIT_SIGNAL & exitSignal);



/**
 *******************************************************************************
 * AVM EVAL MODE
 *******************************************************************************
 */

enum AVM_EXEC_MODE_KIND
{
	AVM_EXEC_STANDALONE_MODE   = 0,

	AVM_EXEC_SERVER_MODE       = 1,

	AVM_EXEC_INTERACTIVE_MODE  = 2
};

extern AVM_EXEC_MODE_KIND  _AVM_EXEC_MODE_;

#define AVM_EXEC_MODE_SET( KIND )  \
	{ _AVM_EXEC_MODE_ = AVM_EXEC_##KIND##_MODE; }

#define AVM_EXEC_MODE_IS( KIND )  \
	( _AVM_EXEC_MODE_ == AVM_EXEC_##KIND##_MODE )


void avm_setExecModeKind(std::string strModeKind);



/**
 *******************************************************************************
 * AVM VERBOSITY LEVEL
 *******************************************************************************
 */

enum AVM_EXEC_VERBOSITY_LEVEL
{
	AVM_EXEC_VERBOSITY_SILENT    = 0,

	AVM_EXEC_VERBOSITY_MINIMUM   = 1,

	AVM_EXEC_VERBOSITY_MEDIUM    = 2,

	AVM_EXEC_VERBOSITY_MAXIMUM   = 3
};

extern AVM_EXEC_VERBOSITY_LEVEL  _AVM_EXEC_VERBOSITY_;


#define AVM_EXEC_VERBOSITY_SET( LEVEL )  \
	{ _AVM_EXEC_VERBOSITY_ = AVM_EXEC_VERBOSITY_##LEVEL; }

#define AVM_EXEC_VERBOSITY_IS( LEVEL )  \
	( _AVM_EXEC_VERBOSITY_ == AVM_EXEC_VERBOSITY_##LEVEL )

#define AVM_EXEC_VERBOSITY_HAS( LEVEL )  \
	( _AVM_EXEC_VERBOSITY_ >= AVM_EXEC_VERBOSITY_##LEVEL )



void avm_setExecVerbosityLevel(std::string strVerbosityLevel);

std::string avm_strExecVerbosityLevel();


/**
 * VERBOSITY TEST
 */
#define _AVM_VERBOSITY_IF_IS_(  LEVEL )  if( AVM_EXEC_VERBOSITY_IS( LEVEL ) ) {

#define _AVM_VERBOSITY_IF_HAS_( LEVEL )  if( AVM_EXEC_VERBOSITY_HAS( LEVEL ) ) {

#define _AVM_VERBOSITY_ELSEIF_( LEVEL )  } else if( AVM_EXEC_VERBOSITY_HAS( LEVEL ) ) {


#define AVM_VERBOSITY_ELSE               } else {

#define AVM_VERBOSITY_ENDIF              } ;


/**
 * VERBOSITY SILENT
 */
#define AVM_VERBOSITY_IF_IS_SILENT       _AVM_VERBOSITY_IF_IS_( SILENT )

#define AVM_VERBOSITY_IF_HAS_SILENT      _AVM_VERBOSITY_IF_HAS_( SILENT )


/**
 * VERBOSITY MINIMUM
 */
#define AVM_VERBOSITY_IF_IS_MINIMUM      _AVM_VERBOSITY_IF_IS_( MINIMUM )

#define AVM_VERBOSITY_IF_HAS_MINIMUM     _AVM_VERBOSITY_IF_HAS_( MINIMUM )

#define AVM_OS_VERBOSITY_MINIMUM( OS )   if( AVM_EXEC_VERBOSITY_HAS( MINIMUM ) ) OS

#define OS_VERBOSITY_MINIMUM_OR_DEBUG( OS )  \
			if( AVM_DEBUG_ENABLED || AVM_EXEC_VERBOSITY_HAS( MINIMUM ) )  OS


/**
 * VERBOSITY MEDIUM
 */
#define AVM_VERBOSITY_IF_IS_MEDIUM       _AVM_VERBOSITY_IF_IS_( MEDIUM )

#define AVM_VERBOSITY_IF_HAS_MEDIUM      _AVM_VERBOSITY_IF_HAS_( MEDIUM )

#define AVM_OS_VERBOSITY_MEDIUM( OS )    if( AVM_EXEC_VERBOSITY_HAS( MEDIUM ) ) OS

#define OS_VERBOSITY_MEDIUM_OR_DEBUG( OS )  \
			if( AVM_DEBUG_ENABLED || AVM_EXEC_VERBOSITY_HAS( MEDIUM ) )  OS


/**
 * VERBOSITY MAXIMUM
 */
#define AVM_VERBOSITY_IF_IS_MAXIMUM      _AVM_VERBOSITY_IF_IS_( MAXIMUM )

#define AVM_VERBOSITY_IF_HAS_MAXIMUM     _AVM_VERBOSITY_IF_HAS_( MAXIMUM )

#define AVM_OS_VERBOSITY_MAXIMUM( OS )   if( AVM_EXEC_VERBOSITY_HAS( MAXIMUM ) ) OS

#define OS_VERBOSITY_MAXIMUM_OR_DEBUG( OS )  \
			if( AVM_DEBUG_ENABLED || AVM_EXEC_VERBOSITY_HAS( MAXIMUM ) )  OS


/**
 * VERBOSITY SWITCH
 */
#define AVM_VERBOSITY_SWITCH               switch( _AVM_EXEC_VERBOSITY_ ) {

#define AVM_VERBOSITY_CASE_SILENT          case AVM_EXEC_VERBOSITY_SILENT : {

#define AVM_VERBOSITY_CASE_MINIMUM         case AVM_EXEC_VERBOSITY_MINIMUM: {

#define AVM_VERBOSITY_CASE_MEDIUM          case AVM_EXEC_VERBOSITY_MEDIUM : {

#define AVM_VERBOSITY_CASE_MAXIMUM         case AVM_EXEC_VERBOSITY_MAXIMUM: {


#define AVM_VERBOSITY_CASE_END             break; }

#define AVM_VERBOSITY_SWITCH_DEFAULT       AVM_VERBOSITY_CASE_END  default: {

#define AVM_VERBOSITY_SWITCH_END           AVM_VERBOSITY_CASE_END }


#define AVM_VERBOSITY_SWITCH_SILENT        AVM_VERBOSITY_SWITCH  AVM_VERBOSITY_CASE_SILENT

#define AVM_VERBOSITY_SWITCH_MINIMUM       AVM_VERBOSITY_SWITCH  AVM_VERBOSITY_CASE_MINIMUM

#define AVM_VERBOSITY_SWITCH_MEDIUM        AVM_VERBOSITY_SWITCH  AVM_VERBOSITY_CASE_MEDIUM

#define AVM_VERBOSITY_SWITCH_MAXIMUM       AVM_VERBOSITY_SWITCH  AVM_VERBOSITY_CASE_MAXIMUM


#define AVM_VERBOSITY_SWITCH_CASE_SILENT   AVM_VERBOSITY_CASE_END  AVM_VERBOSITY_CASE_SILENT

#define AVM_VERBOSITY_SWITCH_CASE_MINIMUM  AVM_VERBOSITY_CASE_END  AVM_VERBOSITY_CASE_MINIMUM

#define AVM_VERBOSITY_SWITCH_CASE_MEDIUM   AVM_VERBOSITY_CASE_END  AVM_VERBOSITY_CASE_MEDIUM

#define AVM_VERBOSITY_SWITCH_CASE_MAXIMUM  AVM_VERBOSITY_CASE_END  AVM_VERBOSITY_CASE_MAXIMUM

#define AVM_VERBOSITY_SWITCH_CASE_MAXIMUM  AVM_VERBOSITY_CASE_END  AVM_VERBOSITY_CASE_MAXIMUM




/**
 *******************************************************************************
 * AVM GLOBAL METHOD
 *******************************************************************************
 */

void avm_report(OutStream & os, const std::string & aMsg, bool forced = false);



}
#endif /*AVM_UTIL_H_*/


