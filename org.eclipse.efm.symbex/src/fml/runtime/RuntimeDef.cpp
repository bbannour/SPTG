/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 févr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "RuntimeDef.h"

#include <util/avm_string.h>

namespace sep
{


/**
 * PROCESS EVAL STATE
 * toString()
 */

#define PRINT_PROCESS_STATE( OBJ )  \
	case PROCESS_##OBJ##_STATE : return( QUOTEME( STATE_##OBJ ) )


std::string RuntimeDef::strPES(PROCESS_EVAL_STATE aPES)
{
	switch ( aPES )
	{
		PRINT_PROCESS_STATE( CREATING );
		PRINT_PROCESS_STATE( CREATED );

		PRINT_PROCESS_STATE( LOADED );

		PRINT_PROCESS_STATE( STARTING );
		PRINT_PROCESS_STATE( INITING );

		PRINT_PROCESS_STATE( FINALIZING );
		PRINT_PROCESS_STATE( FINALIZED );

		PRINT_PROCESS_STATE( DESTROYED );

		PRINT_PROCESS_STATE( STOPPING );
		PRINT_PROCESS_STATE( STOPPED );

		PRINT_PROCESS_STATE( SUSPENDED );

		PRINT_PROCESS_STATE( WAITING );
		PRINT_PROCESS_STATE( WAITING_JOIN );

		PRINT_PROCESS_STATE( ABORTED );
		PRINT_PROCESS_STATE( DISABLED );

//		PRINT_PROCESS_STATE( ENABLED );
		PRINT_PROCESS_STATE( IDLE );

		PRINT_PROCESS_STATE( RUNNING );

		PRINT_PROCESS_STATE( UNDEFINED );

		default :  return( "PROCESS_UNKNOWN_STATE" );
	}
}


/**
 * AVM EXECUTION ENDING STATUS
 * toString()
 */

#define PRINT_AEES( OBJ )   case AEES_##OBJ : return( QUOTEME( AEES_##OBJ ) )


std::string RuntimeDef::strAEES(AVM_EXEC_ENDING_STATUS anAEES)
{
	switch ( anAEES )
	{
		PRINT_AEES( OK );

		PRINT_AEES( FAILED );


		PRINT_AEES( STMNT_NOTHING );

		PRINT_AEES( STMNT_BREAK );

		PRINT_AEES( STMNT_CONTINUE );

		PRINT_AEES( STMNT_RETURN );


		PRINT_AEES( STMNT_FINAL );
		PRINT_AEES( STMNT_DESTROY );

		PRINT_AEES( STMNT_EXIT );
		PRINT_AEES( STMNT_EXIT_ALL );

		PRINT_AEES( STMNT_FATAL_ERROR );

		PRINT_AEES( SYMBOLIC_EXECUTION_LIMITATION );


		PRINT_AEES( STEP_MARK );

		PRINT_AEES( STEP_RESUME );

		PRINT_AEES( WAITING_INCOM_RDV );
		PRINT_AEES( WAITING_OUTCOM_RDV );

		PRINT_AEES( WAITING_JOIN_FORK );

		PRINT_AEES( UNKNOWN_SYNC );

		PRINT_AEES( UNDEFINED );

		default :  return( "AEES_STMNT_UNKNOWN" );
	}
}


/**
 * CONVERSION
 */
AVM_EXEC_ENDING_STATUS RuntimeDef::PES_to_AEES(
		PROCESS_EVAL_STATE aPES, AVM_EXEC_ENDING_STATUS defaultAEES)
{
	switch( aPES )
	{
		case PROCESS_FINALIZED_STATE:
		{
			return AEES_STMNT_FINAL;
		}
		case PROCESS_DESTROYED_STATE:
		{
			return AEES_STMNT_DESTROY;
		}
		default:
		{
			return( defaultAEES );
		}
	}
}


/**
 * SYNCHRONIZATION
 */
PROCESS_EVAL_STATE RuntimeDef::syncPES(PROCESS_EVAL_STATE refPES,
				PROCESS_EVAL_STATE frstPES, PROCESS_EVAL_STATE scndPES)
{
	if( (refPES == scndPES) || (frstPES == scndPES) )
	{
		return( frstPES );
	}
	else if( refPES == frstPES )
	{
		return( scndPES );
	}
	else if( (frstPES == PROCESS_WAITING_JOIN_STATE) ||
			 (scndPES == PROCESS_WAITING_JOIN_STATE) )
	{
		return( PROCESS_WAITING_JOIN_STATE );
	}

	return( PROCESS_UNDEFINED_STATE );
}


AVM_EXEC_ENDING_STATUS RuntimeDef::syncAEES(
		AVM_EXEC_ENDING_STATUS frstAEES, AVM_EXEC_ENDING_STATUS scndAEES)
{
	if( frstAEES == scndAEES )
	{
		return( frstAEES );
	}

	else if( frstAEES == AEES_STMNT_NOTHING )
	{
		return( scndAEES );
	}
	else if( scndAEES == AEES_STMNT_NOTHING )
	{
		return( frstAEES );
	}

	else if( (frstAEES == AEES_STMNT_EXIT_ALL) ||
			 (scndAEES == AEES_STMNT_EXIT_ALL) )
	{
		return( AEES_STMNT_EXIT_ALL );
	}
	else if( (frstAEES == AEES_STMNT_EXIT) ||
			 (scndAEES == AEES_STMNT_EXIT) )
	{
		return( AEES_STMNT_EXIT );
	}
	else if( (frstAEES == AEES_STMNT_FATAL_ERROR) ||
			 (scndAEES == AEES_STMNT_FATAL_ERROR) )
	{
		return( AEES_STMNT_FATAL_ERROR );
	}

	else if( (frstAEES == AEES_SYMBOLIC_EXECUTION_LIMITATION) ||
			 (scndAEES == AEES_SYMBOLIC_EXECUTION_LIMITATION) )
	{
		return( AEES_SYMBOLIC_EXECUTION_LIMITATION );
	}

	return( AEES_UNKNOWN_SYNC );
}


} /* namespace sep */
