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

#ifndef RUNTIMEDEF_H_
#define RUNTIMEDEF_H_

#include <string>

#include <fml/operator/OperatorLib.h>


namespace sep
{


enum PROCESS_EVAL_STATE
{
	PROCESS_CREATING_STATE,
	PROCESS_CREATED_STATE,

	PROCESS_LOADED_STATE,

	PROCESS_STARTING_STATE,
	PROCESS_INITING_STATE,

	PROCESS_FINALIZING_STATE,
	PROCESS_FINALIZED_STATE,
	PROCESS_DESTROYED_STATE,

	PROCESS_STOPPING_STATE,
	PROCESS_STOPPED_STATE,

//	PROCESS_SLEEPING_STATE,
	PROCESS_SUSPENDED_STATE,

	PROCESS_WAITING_STATE,
	PROCESS_WAITING_JOIN_STATE,

	PROCESS_ABORTED_STATE,
	PROCESS_DISABLED_STATE,

//	PROCESS_ENABLED_STATE,
	PROCESS_IDLE_STATE,

	PROCESS_RUNNING_STATE,
	PROCESS_RTC_STATE,

	PROCESS_UNDEFINED_STATE
};


enum AVM_EXECUTION_ENDING_STATUS
{
	AEES_OK,
	AEES_FAILED,

	AEES_STMNT_NOTHING,

	AEES_STMNT_BREAK,
	AEES_STMNT_CONTINUE,
	AEES_STMNT_RETURN,

	AEES_STMNT_FINAL,
	AEES_STMNT_DESTROY,

	AEES_STMNT_EXIT,
	AEES_STMNT_EXIT_ALL,

	AEES_STMNT_FATAL_ERROR,

	AEES_SYMBOLIC_EXECUTION_LIMITATION,

	AEES_STEP_MARK,
	AEES_STEP_RESUME,

	AEES_WAITING_INCOM_RDV,
	AEES_WAITING_OUTCOM_RDV,

	AEES_WAITING_JOIN_FORK,

	AEES_UNKNOWN_SYNC,

	AEES_UNDEFINED
};



class RuntimeDef
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RuntimeDef()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~RuntimeDef()
	{
		//!! NOTHING
	}


	/**
	 * toString()
	 */
	static std::string strPES(PROCESS_EVAL_STATE aPES);

	static std::string strAEES(AVM_EXECUTION_ENDING_STATUS anAEES);


	/**
	 * CONVERSION
	 */
	static AVM_EXECUTION_ENDING_STATUS PES_to_AEES(
			PROCESS_EVAL_STATE aPES, AVM_EXECUTION_ENDING_STATUS defaultAEES);

	static PROCESS_EVAL_STATE Opcode_to_PES(AVM_OPCODE opcode);


	/**
	 * SYNCHRONIZATION
	 */
	static PROCESS_EVAL_STATE syncPES(PROCESS_EVAL_STATE refState,
				PROCESS_EVAL_STATE frstState, PROCESS_EVAL_STATE scndState);

	static AVM_EXECUTION_ENDING_STATUS syncAEES(
			AVM_EXECUTION_ENDING_STATUS frstAEES,
			AVM_EXECUTION_ENDING_STATUS scndAEES);




};



} /* namespace sep */
#endif /* RUNTIMEDEF_H_ */
