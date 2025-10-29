/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ITRACEPOINT_H_
#define ITRACEPOINT_H_

#include <fml/lib/IComPoint.h>

#include <fml/operator/OperatorLib.h>


namespace sep
{


class ITracePoint
{
public:


};


////////////////////////////////////////////////////////////////////////////////
// TRACE POINT
////////////////////////////////////////////////////////////////////////////////

class ENUM_TRACE_POINT
{

public:

	enum TRACE_NATURE
	{
		TRACE_COMPOSITE_NATURE,


		TRACE_COM_NATURE,

		TRACE_CHANNEL_NATURE,

		TRACE_MESSAGE_NATURE,

		TRACE_PORT_NATURE,

		TRACE_SIGNAL_NATURE,

		TRACE_BUFFER_NATURE,


		TRACE_TIME_NATURE,

		TRACE_VARIABLE_NATURE,

		TRACE_FORMULA_NATURE,

		TRACE_CONDITION_NATURE,
		TRACE_DECISION_NATURE,

		TRACE_PATH_CONDITION_NATURE,
		TRACE_PATH_CONDITION_NATURE_LEAF,

		TRACE_PATH_TIMED_CONDITION_NATURE,
		TRACE_PATH_TIMED_CONDITION_NATURE_LEAF,

		TRACE_NODE_CONDITION_NATURE,
		TRACE_NODE_CONDITION_NATURE_LEAF,

		TRACE_NODE_TIMED_CONDITION_NATURE,
		TRACE_NODE_TIMED_CONDITION_NATURE_LEAF,

		TRACE_MACHINE_NATURE,

		TRACE_STATE_NATURE,

		TRACE_STATEMACHINE_NATURE,


		TRACE_TRANSITION_NATURE,

		TRACE_ROUTINE_NATURE,

		TRACE_RUNNABLE_NATURE,

		TRACE_EXECUTION_INFORMATION_NATURE,

		TRACE_META_TRACE_NATURE,
		TRACE_META_DEBUG_NATURE,

		// VIRTUAL ELEMENT
		TRACE_COMMENT_NATURE,
		TRACE_SEPARATOR_NATURE,
		TRACE_NEWLINE_NATURE,

		TRACE_INIT_HEADER_NATURE,
		TRACE_INIT_BEGIN_NATURE,
		TRACE_INIT_END_NATURE,

		TRACE_STEP_HEADER_NATURE,
		TRACE_STEP_BEGIN_NATURE,
		TRACE_STEP_END_NATURE,

		TRACE_UNDEFINED_NATURE,
		TRACE_NULL_NATURE
	};


	/**
	 * CONSTANTS
	 * ATTRIBUTE ID
	 */
	static const std::string ATTRIBUTE_EXECUTION_INFORMATION_ID;


	/**
	 * STATIC
	 */
	static TRACE_NATURE to_nature(IComPoint::ENUM_IO_NATURE io);

	static TRACE_NATURE to_nature(const std::string & id);


	static bool is_com(TRACE_NATURE nature);

	static bool is_com(const std::string & id);


	static std::string to_string(TRACE_NATURE nature);

	static std::string to_uid(TRACE_NATURE nature, AVM_OPCODE op);

};


} /* namespace sep */

#endif /* ITRACEPOINT_H_ */
