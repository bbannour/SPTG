/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompositePart.h"

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/Transition.h>


namespace sep
{


/**
 * GETTER
 * EXECUTABLE MACHINE COUNT
 */
std::size_t CompositePart::getExecutableMachineCount() const
{
	std::size_t theExecutableCount = 0;

	const_machine_iterator itMachine = machine_begin();
	const_machine_iterator endMachine = machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( itMachine->getSpecifier().hasDesignModel() )
		{
			theExecutableCount += itMachine->getExecutableMachineCount();
		}
	}

//	const_state_iterator itState = state_begin();
//	const_state_iterator endState = state_end();
//	for( ; itState != endState ; ++itState )
//	{
//		theExecutableCount += itState->getExecutableMachineCount();
//	}

	const_procedure_iterator itProcedure = procedure_begin();
	const_procedure_iterator endProcedure = procedure_end();
	for( ; itProcedure != endProcedure ; ++itProcedure )
	{
		theExecutableCount += itProcedure->getExecutableMachineCount();
	}


	return( theExecutableCount );
}


/**
 * DISPATCH
 * mOwnedElements
 */
void CompositePart::dispatchOwnedElement(BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	Machine & aMachine = anElement.to< Machine >();

	if( aMachine.getSpecifier().isDesignInstanceStatic() )
	{
		mMachines.append( anElement );

		aMachine.setRuntimeOffset( mInstanceStatics.size() );

		mInstanceStatics.append( anElement );
	}
	else if( aMachine.getSpecifier().isDesignInstanceDynamic() )
	{
		aMachine.setRuntimeOffset( mInstanceStatics.size() );

		mInstanceDynamics.append( anElement );
	}
	else if( aMachine.getSpecifier().isFamilyComponentState() )
	{
		mMachines.append( anElement );

		aMachine.setRuntimeOffset( mStates.size() );

		mStates.append( anElement );
	}
	else if( aMachine.getSpecifier().isComponentProcedure() )
	{
		aMachine.setRuntimeOffset( mProcedures.size() );

		mProcedures.append( anElement );
	}
	else
	{
		aMachine.setRuntimeOffset( mMachines.size() );

		mMachines.append( anElement );
	}
}


/**
 * GETTER - SETTER
 * mOutgoingTransitions
 */
void CompositePart::appendOutgoingTransitionToEveryState(Machine & aGroupState)
{
	if( aGroupState.hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState.getBehavior();
		BehavioralPart::transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::transition_iterator itTransition;
		Transition * newTransition;

		CompositePart * aGroupCompositePart = aGroupState.getCompositePart();
		state_iterator itMachine = aGroupCompositePart->state_begin();
		state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask()) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition(itMachine, itTransition);

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}


void CompositePart::appendOutgoingTransitionToSomeState(Machine & aGroupState)
{
	if( aGroupState.hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState.getBehavior();
		BehavioralPart::transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::transition_iterator itTransition;
		Transition * newTransition;

		const ListOfString & listofId = aGroupState.getGroupId();

		CompositePart * aGroupCompositePart = aGroupState.getCompositePart();
		state_iterator itMachine = aGroupCompositePart->state_begin();
		state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask())
				&& listofId.contains((itMachine)->getNameID()) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition(itMachine, itTransition);

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}

void CompositePart::appendOutgoingTransitionToExceptState(Machine & aGroupState)
{
	if( aGroupState.hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState.getBehavior();
		BehavioralPart::transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::transition_iterator itTransition;
		Transition * newTransition;

		const ListOfString & listofId = aGroupState.getGroupId();

		CompositePart * aGroupCompositePart = aGroupState.getCompositePart();
		state_iterator itMachine = aGroupCompositePart->state_begin();
		state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask())
				&& (not listofId.contains((itMachine)->getNameID())) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition(itMachine, itTransition);

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}


void CompositePart::expandGroupStatemachine()
{
	state_iterator itState = state_begin();
	state_iterator endState = state_end();
	for( ; itState != endState ; ++itState )
	{
		if( (itState)->getSpecifier().hasGroupMask() )
		{
			if( (itState)->getSpecifier().isGroupEvery())
			{
				appendOutgoingTransitionToEveryState( itState );
			}
			else if( (itState)->getSpecifier().isGroupSome())
			{
				appendOutgoingTransitionToSomeState( itState );
			}
			else if( (itState)->getSpecifier().isGroupExcept() )
			{
				appendOutgoingTransitionToExceptState( itState );
			}
		}
	}
}


/**
 * Serialization
 */
void CompositePart::toStream(OutStream & out) const
{
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	//
AVM_IF_DEBUG_FLAG2_AND( COMPILING , STATEMACHINE , mOwnedElements.nonempty() )
	out << EOL << TAB << "/*owned< executable#count = "
			<< getExecutableMachineCount() << " > [" << EOL_INCR_INDENT
			<< str_header( mOwnedElements ) << DECR_INDENT_TAB
			<< "] // end owned*/" << EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG2_AND( COMPILING , STATEMACHINE )
	//
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	if( hasProcedure() )
	{
		out << EOL_TAB << "@procedure:" << INCR_INDENT;
		const_procedure_iterator itProcedure = procedure_begin();
		const_procedure_iterator endProcedure = procedure_end();
		for( ; itProcedure != endProcedure ; ++itProcedure )
		{
			out << EOL;
			(itProcedure)->toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasState() )
	{
		const std::string & sequenceName = ( getContainerMachine()->
				getSpecifier().isComponentStatemachine() ?
						"region" : "statemachine" );

//AVM_IF_DEBUG_FLAG2( COMPILING , STATEMACHINE )
//		out << EOL_TAB << "/*" << sequenceName << ": [" << EOL_INCR_INDENT
//			<< str_header( mStates ) << DECR_INDENT_TAB
//			<< "] // end " << sequenceName << "*/" << EOL2_FLUSH;
//AVM_ENDIF_DEBUG_FLAG2( COMPILING , STATEMACHINE )

		out << EOL_TAB << "@" << sequenceName << ":" << INCR_INDENT;

		const_state_iterator itState = state_begin();
		const_state_iterator endState = state_end();
		for( ; itState != endState ; ++itState )
		{
			out << EOL;
			(itState)->toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasMachine() && (getMachines().size() >
			(getStates().size() + getInstanceStatics().size())) )
	{
		out << EOL_TAB << "@" << getNameID() << ":" << INCR_INDENT;

		const_machine_iterator it = machine_begin();
		const_machine_iterator endIt = machine_end();
		for( ; it != endIt ; ++it )
		{
			if( (not (it)->getSpecifier().isFamilyComponentState())
				&& (not (it)->getSpecifier().isDesignInstanceStatic()) )
			{
				out << EOL;
				(it)->toStream(out);
			}
		}
		out << DECR_INDENT;
	}

	if( hasInstanceStatic() )
	{
//AVM_IF_DEBUG_FLAG2( COMPILING , STATEMACHINE )
//		out << EOL_TAB << "/*instance: [" << EOL_INCR_INDENT
//			<< str_header( mInstanceStatics ) << DECR_INDENT_TAB
//			<< "] // end instance*/" << EOL_FLUSH;
//AVM_ENDIF_DEBUG_FLAG2( COMPILING , STATEMACHINE )

		out << EOL_TAB << "@instance:" << EOL_INCR_INDENT;

		const_instance_iterator it = instance_static_begin();
		const_instance_iterator endIt = instance_static_end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(out);
		}
		out << DECR_INDENT;
	}

	if( hasInstanceDynamic() )
	{
//AVM_IF_DEBUG_FLAG2( COMPILING , STATEMACHINE )
//	out << EOL_TAB << "/*#dynamic instance: [" << EOL_INCR_INDENT
//			<< str_header( mInstanceDynamics ) << DECR_INDENT_TAB
//			<< "] // end dynamic*/" << EOL2_FLUSH;
//AVM_ENDIF_DEBUG_FLAG2( COMPILING , STATEMACHINE )

		out << EOL_TAB << "@instance#dynamic:" << INCR_INDENT;
		const_machine_iterator it = instance_dynamic_begin();
		const_machine_iterator endIt = instance_dynamic_end();
		for( ; it != endIt ; ++it )
		{
			out << EOL;
			(it)->toStream(out);
		}
		out << DECR_INDENT;
	}

	out << std::flush;
}


} /* namespace sep */
