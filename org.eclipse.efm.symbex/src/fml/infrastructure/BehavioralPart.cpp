/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BehavioralPart.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Transition.h>


namespace sep
{


/**
 * UTIL
 */
Routine & BehavioralPart::getActivity(AVM_OPCODE opcodeActivity)
{
	switch( opcodeActivity )
	{
		case AVM_OPCODE_INVOKE_NEW : return( onCreateRoutine  );

		case AVM_OPCODE_INIT   : return( onInitRoutine  );
		case AVM_OPCODE_FINAL  : return( onReturnRoutine );

		case AVM_OPCODE_RETURN : return( onReturnRoutine );

		case AVM_OPCODE_START  : return( onStartRoutine );
		case AVM_OPCODE_STOP   : return( onStopRoutine  );

		case AVM_OPCODE_IENABLE_INVOKE : return( onIEnableRoutine );
		case AVM_OPCODE_ENABLE_INVOKE  : return( onEnableRoutine  );

		case AVM_OPCODE_IDISABLE_INVOKE: return( onIDisableRoutine );
		case AVM_OPCODE_DISABLE_INVOKE : return( onDisableRoutine  );

		case AVM_OPCODE_IABORT_INVOKE  : return( onIAbortRoutine );
		case AVM_OPCODE_ABORT_INVOKE   : return( onAbortRoutine  );

		case AVM_OPCODE_IRUN: return( onIRunRoutine );
		case AVM_OPCODE_RUN : return( onRunRoutine  );
		case AVM_OPCODE_RTC : return( onRtcRoutine  );

		case AVM_OPCODE_SCHEDULE_INVOKE: return( onScheduleRoutine );

		case AVM_OPCODE_SYNCHRONIZE    : return( onSynchronizeRoutine );

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BehavioralPart::getActivity:> Unknown Activity !!!"
					<< SEND_EXIT;

			return( onRunRoutine );
		}
	}
}

const Routine & BehavioralPart::getActivity(AVM_OPCODE opcodeActivity) const
{
	switch( opcodeActivity )
	{
		case AVM_OPCODE_INVOKE_NEW    : return( onCreateRoutine  );

		case AVM_OPCODE_INIT   : return( onInitRoutine  );
		case AVM_OPCODE_FINAL  : return( onReturnRoutine );

		case AVM_OPCODE_RETURN : return( onReturnRoutine );

		case AVM_OPCODE_START  : return( onStartRoutine );
		case AVM_OPCODE_STOP   : return( onStopRoutine  );

		case AVM_OPCODE_IENABLE_INVOKE : return( onIEnableRoutine );
		case AVM_OPCODE_ENABLE_INVOKE  : return( onEnableRoutine  );

		case AVM_OPCODE_IDISABLE_INVOKE: return( onIDisableRoutine );
		case AVM_OPCODE_DISABLE_INVOKE : return( onDisableRoutine  );

		case AVM_OPCODE_IABORT_INVOKE  : return( onIAbortRoutine );
		case AVM_OPCODE_ABORT_INVOKE   : return( onAbortRoutine  );

		case AVM_OPCODE_IRUN: return( onIRunRoutine );
		case AVM_OPCODE_RUN : return( onRunRoutine  );
		case AVM_OPCODE_RTC : return( onRtcRoutine  );

		case AVM_OPCODE_SCHEDULE_INVOKE: return( onScheduleRoutine );

		case AVM_OPCODE_SYNCHRONIZE    : return( onSynchronizeRoutine );

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BehavioralPart::getActivity:> Unknown Activity !!!"
					<< SEND_EXIT;

			return( onRunRoutine );
		}
	}
}


/**
 * Serialization
 */
void BehavioralPart::toStreamRoutine(OutStream & os) const
{
	os << TAB << "routine:" << EOL_INCR_INDENT;

	const_routine_iterator it = mRoutines.begin();
	const_routine_iterator endIt = mRoutines.end();
	for( ; it != endIt ; ++it )
	{
		(it)->toStream(os);
	}

	os << DECR_INDENT;
}

void BehavioralPart::toStreamAnonymousInnerRoutine(OutStream & os) const
{
	os << TAB << "/*routine< anonymous#inner >: [" << EOL;

	const_routine_iterator it = mAnonymousInnerRoutines.begin();
	const_routine_iterator endIt = mAnonymousInnerRoutines.end();
	for( ; it != endIt ; ++it )
	{
		os << TAB2 << (it)->getFullyQualifiedNameID() << ";" << EOL;
//		os << TAB2 << str_header( *it ) << ";" << EOL;
	}
	os << TAB << "] // end routine" << "*/" << EOL2_FLUSH;
}


void BehavioralPart::toStreamMoe(OutStream & os) const
{
	/**
	 * Transitions Part
	 */
	if( hasOutgoingTransition() )
	{
		if( not getContainerMachine()->getSpecifier().isStateBasic() )
		{
			os << TAB << "transition" /*<< "< outgoing >"*/ << ":" << EOL;
		}

		os << INCR_INDENT;
		const_transition_iterator it = outgoing_transition_begin();
		const_transition_iterator endIt = outgoing_transition_end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(os);
		}
		os << DECR_INDENT;
	}

	if( hasIncomingTransition() )
	{
		os << TAB << "/*transition< incoming >: [" << EOL_INCR_INDENT;
		const_transition_iterator it = incoming_transition_begin();
		const_transition_iterator endIt = incoming_transition_end();
		for( ; it != endIt ; ++it )
		{
			os << TAB2 << str_header( *it ) << ";" << EOL;
		}
		os << DECR_INDENT_TAB << "] // end transition" << "*/" << EOL_FLUSH;
	}


	if( getContainer()->isnot< Machine >() ||
		(not getContainerMachine()->getSpecifier().isStateBasic()) )
	{
		os << TAB << getNameID() << ":" << EOL;
	}

	/**
	 * Routines Part
	 */
	os << INCR_INDENT;

	if( hasOnCreate() )
	{
		getOnCreateRoutine().toStream(os);
	}

	if( hasOnInit() )
	{
		getOnInitRoutine().toStream(os);
	}

	if( hasOnFinal() )
	{
		getOnFinalRoutine().toStream(os);
	}

	if( hasOnReturn() )
	{
		getOnReturnRoutine().toStream(os);
	}


	if( hasOnStart() )
	{
		getOnStartRoutine().toStream(os);
	}

	if( hasOnStop() )
	{
		getOnStopRoutine().toStream(os);
	}


	if( hasOnIEnable() )
	{
		getOnIEnableRoutine().toStream(os);
	}

	if( hasOnEnable() )
	{
		getOnEnableRoutine().toStream(os);
	}


	if( hasOnIDisable() )
	{
		getOnIDisableRoutine().toStream(os);
	}

	if( hasOnDisable() )
	{
		getOnDisableRoutine().toStream(os);
	}


	if( hasOnIAbort() )
	{
		getOnIAbortRoutine().toStream(os);
	}

	if( hasOnAbort() )
	{
		getOnAbortRoutine().toStream(os);
	}


	if( hasOnIRun() )
	{
		getOnIRunRoutine().toStream(os);
	}

	if( hasOnRun() )
	{
		getOnRunRoutine().toStream(os);
	}


	if( hasOnRtc() )
	{
		getOnRtcRoutine().toStream(os);
	}


	if( hasOnConcurrency() )
	{
		getOnConcurrencyRoutine().toStream(os);
	}

	if( hasOnSchedule() )
	{
		getOnScheduleRoutine().toStream(os);
	}

	if( hasOnSynchronize() )
	{
		getOnSynchronizeRoutine().toStream(os);
	}

	os << DECR_INDENT;
}



}
