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

#include "ITracePoint.h"

#include <fml/workflow/Query.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// TRACE POINT
////////////////////////////////////////////////////////////////////////////////

ENUM_TRACE_POINT::TRACE_NATURE ENUM_TRACE_POINT::to_nature(
		IComPoint::ENUM_IO_NATURE io)
{
	switch( io )
	{
		case IComPoint::IO_CHANNEL_NATURE   : return( TRACE_CHANNEL_NATURE );

		case IComPoint::IO_MESSAGE_NATURE   : return( TRACE_MESSAGE_NATURE );

		case IComPoint::IO_PORT_NATURE      : return( TRACE_PORT_NATURE );

		case IComPoint::IO_SIGNAL_NATURE    : return( TRACE_SIGNAL_NATURE );

		case IComPoint::IO_UNDEFINED_NATURE : return( TRACE_UNDEFINED_NATURE );

		default                             : return( TRACE_UNDEFINED_NATURE );
	}
}


ENUM_TRACE_POINT::TRACE_NATURE ENUM_TRACE_POINT::to_nature(
		const std::string & id)
{
	if( id == "com"          ) return TRACE_COM_NATURE;

	if( id == "channel"      ) return TRACE_CHANNEL_NATURE;

	if( id == "message"      ) return TRACE_MESSAGE_NATURE;

	if( id == "port"         ) return TRACE_PORT_NATURE;

	if( id == "signal"       ) return TRACE_SIGNAL_NATURE;

	if( id == "time"         ) return TRACE_TIME_NATURE;

	if( id == "var"          ) return TRACE_VARIABLE_NATURE;
	if( id == "variable"     ) return TRACE_VARIABLE_NATURE;
//	if( id == "assign"       ) return TRACE_VARIABLE_NATURE;
//	if( id == "newfresh"     ) return TRACE_VARIABLE_NATURE;

	if( id == "buffer"       ) return TRACE_BUFFER_NATURE;

	if( id == "formula"      ) return TRACE_FORMULA_NATURE;

	if( id == "condition"    ) return TRACE_CONDITION_NATURE;
	if( id == "decision"     ) return TRACE_DECISION_NATURE;

	if( REGEX_MATCH(id, CONS_WID2("path", "condition")) ) return TRACE_PATH_CONDITION_NATURE;
	if( REGEX_MATCH(id, CONS_WID2("node", "condition")) ) return TRACE_NODE_CONDITION_NATURE;

	if( REGEX_MATCH(id, CONS_WID3("path", "condition", "leaf")) ) {
		return TRACE_PATH_CONDITION_NATURE_LEAF;
	}
	if( REGEX_MATCH(id, CONS_WID3("node", "condition", "leaf")) ) {
		return TRACE_NODE_CONDITION_NATURE_LEAF;
	}

	if( REGEX_MATCH(id, CONS_WID3("path", "timed", "condition")) ) {
		return TRACE_PATH_TIMED_CONDITION_NATURE;
	}
	if( REGEX_MATCH(id, CONS_WID3("node", "timed", "condition")) ) {
		return TRACE_NODE_TIMED_CONDITION_NATURE;
	}

	if( REGEX_MATCH(id, CONS_WID4(
			"path", "timed", "condition", "(leaf|end|last|tail)")) ) {
		return TRACE_PATH_TIMED_CONDITION_NATURE_LEAF;
	}
	if( REGEX_MATCH(id, CONS_WID4(
			"node", "timed", "condition", "(leaf|end|last|tail)")) ) {
		return TRACE_NODE_TIMED_CONDITION_NATURE_LEAF;
	}

	if( id == "machine"      ) return TRACE_MACHINE_NATURE;
	if( id == "state"        ) return TRACE_STATE_NATURE;
	if( id == "statemachine" ) return TRACE_STATEMACHINE_NATURE;

	if( id == "transition"   ) return TRACE_TRANSITION_NATURE;
	if( id == "routine"      ) return TRACE_ROUTINE_NATURE;

	if( id == "runnable"     ) return TRACE_RUNNABLE_NATURE;

	if( REGEX_MATCH(id, CONS_WID2(
			"init", "header")) ) return TRACE_INIT_HEADER_NATURE;

	if( REGEX_MATCH(id, CONS_WID2(
			"init", "begin" )) ) return TRACE_INIT_BEGIN_NATURE;

	if( REGEX_MATCH(id, CONS_WID2(
			"init", "end"   )) ) return TRACE_INIT_END_NATURE;


	if( REGEX_MATCH(id, CONS_WID2(
			"step", "header")) ) return TRACE_STEP_HEADER_NATURE;

	if( REGEX_MATCH(id, CONS_WID2(
			"step", "begin" )) ) return TRACE_STEP_BEGIN_NATURE;

	if( REGEX_MATCH(id, CONS_WID2(
			"step", "end"   )) ) return TRACE_STEP_END_NATURE;


	if( id == "comment"      ) return TRACE_COMMENT_NATURE;
	if( id == "separator"    ) return TRACE_SEPARATOR_NATURE;
	if( id == "newline"      ) return TRACE_NEWLINE_NATURE;

	if( id == "composite"    ) return TRACE_COMPOSITE_NATURE;
	if( id == "trace"        ) return TRACE_COMPOSITE_NATURE;
	if( id == "point"        ) return TRACE_COMPOSITE_NATURE;

	return TRACE_UNDEFINED_NATURE;
}


bool ENUM_TRACE_POINT::is_com(ENUM_TRACE_POINT::TRACE_NATURE nature)
{
	switch( nature )
	{
		case TRACE_COM_NATURE     :
		case TRACE_CHANNEL_NATURE :
		case TRACE_MESSAGE_NATURE :
		case TRACE_PORT_NATURE    :
		case TRACE_SIGNAL_NATURE  : return( true );

		default                   : return( false );
	}
}

bool ENUM_TRACE_POINT::is_com(const std::string & id)
{
	if( (id == "com"     ) ||
		(id == "channel" ) ||
		(id == "message" ) ||
		(id == "port"    ) ||
		(id == "signal"  ) )
	{
		return true;
	}

	return( false );
}


std::string ENUM_TRACE_POINT::to_string(ENUM_TRACE_POINT::TRACE_NATURE nature)
{
	switch( nature )
	{
		case TRACE_COMPOSITE_NATURE    : return( "composite" );

		case TRACE_COM_NATURE          : return( "com"       );

		case TRACE_CHANNEL_NATURE      : return( "channel"   );
		case TRACE_MESSAGE_NATURE      : return( "message"   );

		case TRACE_PORT_NATURE         : return( "port"      );
		case TRACE_SIGNAL_NATURE       : return( "signal"    );

		case TRACE_TIME_NATURE         : return( "time"      );
		case TRACE_VARIABLE_NATURE     : return( "variable"  );
		case TRACE_BUFFER_NATURE       : return( "buffer"    );

		case TRACE_FORMULA_NATURE      : return( "formula"   );

		case TRACE_CONDITION_NATURE    : return( "condition" );
		case TRACE_DECISION_NATURE     : return( "decision"  );

		case TRACE_PATH_CONDITION_NATURE  : return( "path#conditon" );
		case TRACE_NODE_CONDITION_NATURE  : return( "node#conditon" );

		case TRACE_PATH_CONDITION_NATURE_LEAF : return( "path#conditon#leaf" );
		case TRACE_NODE_CONDITION_NATURE_LEAF : return( "node#conditon#leaf" );

		case TRACE_PATH_TIMED_CONDITION_NATURE: return( "path#timed#conditon" );
		case TRACE_NODE_TIMED_CONDITION_NATURE: return( "node#timed#conditon" );

		case TRACE_PATH_TIMED_CONDITION_NATURE_LEAF: return( "path#timed#conditon#leaf" );
		case TRACE_NODE_TIMED_CONDITION_NATURE_LEAF: return( "node#timed#conditon#leaf" );

		case TRACE_MACHINE_NATURE      : return( "machine"      );
		case TRACE_STATE_NATURE        : return( "state"        );
		case TRACE_STATEMACHINE_NATURE : return( "statemachine" );

		case TRACE_TRANSITION_NATURE   : return( "transition" );
		case TRACE_ROUTINE_NATURE      : return( "routine"    );

		case TRACE_RUNNABLE_NATURE     : return( "runnable" );

		case TRACE_STEP_HEADER_NATURE  : return( "step#header" );
		case TRACE_STEP_BEGIN_NATURE   : return( "step#begin"  );
		case TRACE_STEP_END_NATURE     : return( "step#end"    );

		case TRACE_INIT_HEADER_NATURE  : return( "init#header" );
		case TRACE_INIT_BEGIN_NATURE   : return( "init#begin"  );
		case TRACE_INIT_END_NATURE     : return( "init#end"    );

		case TRACE_COMMENT_NATURE      : return( "comment" );
		case TRACE_SEPARATOR_NATURE    : return( "separator" );
		case TRACE_NEWLINE_NATURE      : return( "newline" );

		case TRACE_UNDEFINED_NATURE    : return( "undefined<point#nature>" );

		default                        : return( "unknown<point#nature>"   );
	}
}


std::string ENUM_TRACE_POINT::to_uid(
		ENUM_TRACE_POINT::TRACE_NATURE nature, AVM_OPCODE op)
{
	switch( nature )
	{
		case TRACE_COMPOSITE_NATURE    : return( "composite" );

		case TRACE_COM_NATURE          : return( "com"     );

		case TRACE_CHANNEL_NATURE      : return( "channel" );
		case TRACE_MESSAGE_NATURE      : return( "message" );

		case TRACE_PORT_NATURE         : return( "port"    );
		case TRACE_SIGNAL_NATURE       : return( "signal"  );

		case TRACE_TIME_NATURE         : return( "time"  );

		case TRACE_VARIABLE_NATURE     :
		{
			switch( op )
			{
				case AVM_OPCODE_ASSIGN         : return( "assign"   );
				case AVM_OPCODE_ASSIGN_NEWFRESH: return( "newfresh" );
				default                        : return( "variable" );
			}
			return( "variable" );
		}

		case TRACE_BUFFER_NATURE       : return( "buffer"    );

		case TRACE_FORMULA_NATURE      : return( "formula"   );

		case TRACE_CONDITION_NATURE    : return( "condition" );
		case TRACE_DECISION_NATURE     : return( "decision"  );

		case TRACE_PATH_CONDITION_NATURE : return( "path#conditon" );
		case TRACE_NODE_CONDITION_NATURE : return( "node#conditon" );

		case TRACE_PATH_CONDITION_NATURE_LEAF: return( "path#conditon#leaf" );
		case TRACE_NODE_CONDITION_NATURE_LEAF: return( "node#conditon#leaf" );

		case TRACE_PATH_TIMED_CONDITION_NATURE: return( "path#timed#conditon" );
		case TRACE_NODE_TIMED_CONDITION_NATURE: return( "node#timed#conditon" );

		case TRACE_PATH_TIMED_CONDITION_NATURE_LEAF: return( "path#timed#conditon#leaf" );
		case TRACE_NODE_TIMED_CONDITION_NATURE_LEAF: return( "node#timed#conditon#leaf" );

		case TRACE_MACHINE_NATURE      : return( "machine"      );
		case TRACE_STATE_NATURE        : return( "state"        );
		case TRACE_STATEMACHINE_NATURE : return( "statemachine" );

		case TRACE_TRANSITION_NATURE   : return( "transition"   );
		case TRACE_ROUTINE_NATURE      : return( "routine"      );

		case TRACE_RUNNABLE_NATURE     : return( "runnable"     );

		case TRACE_STEP_HEADER_NATURE  : return( "step#header"  );
		case TRACE_STEP_BEGIN_NATURE   : return( "step#begin"   );
		case TRACE_STEP_END_NATURE     : return( "step#end"     );

		case TRACE_INIT_HEADER_NATURE  : return( "init#header"  );
		case TRACE_INIT_BEGIN_NATURE   : return( "init#begin"   );
		case TRACE_INIT_END_NATURE     : return( "init#end"     );

		case TRACE_COMMENT_NATURE      : return( "comment"      );
		case TRACE_SEPARATOR_NATURE    : return( "separator"    );
		case TRACE_NEWLINE_NATURE      : return( "newline"      );

		case TRACE_UNDEFINED_NATURE    : return( "undefined<point#nature>" );

		default                        : return( "unknown<point#nature>"   );
	}
}



} /* namespace sep */
