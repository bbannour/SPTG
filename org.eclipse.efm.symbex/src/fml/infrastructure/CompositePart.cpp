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
 * COPY TO
 */
void CompositePart::copyMachineTo(
		Collection< Machine * > & rawContainer) const
{
	const_machine_iterator it = machine_begin();
	const_machine_iterator endIt = machine_end();
	for( ; it != endIt ; ++it )
	{
		rawContainer.append( it );
	}
}


/**
 * GETTER for PARSER / COMPILER
 * Machine
 */
Machine * CompositePart::rawExecutableMachineByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	return( mMachines.rawByNameID(aQualifiedNameID) );

	const_machine_iterator it = machine_begin();
	const_machine_iterator endIt = machine_end();
	for( ; it != endIt ; ++it )
	{
		if( (it)->getSpecifier().hasDesignModel()
			&& (it)->fqnEndsWith(aQualifiedNameID) )
		{
			return( it );
		}
	}
	return( NULL );
}


/**
 * DISPATCH
 * mOwnedElements
 */
void CompositePart::dispatchOwnedElement(const BF & anElement)
{
	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( anElement )
			<< "Executable Machine owned element !!!"
			<< SEND_EXIT;

	Machine * aMachine = anElement.to_ptr< Machine >();

	if( aMachine->getSpecifier().isDesignInstanceStatic() )
	{
		appendMachine( anElement );

		appendInstanceStatic( anElement );
	}
	else if( aMachine->getSpecifier().isDesignInstanceDynamic() )
	{
		appendInstanceDynamic( anElement );
	}
	else if( aMachine->getSpecifier().isFamilyComponentState() )
	{
		appendMachine( anElement );

		appendState( anElement );
	}
	else if( aMachine->getSpecifier().isComponentProcedure() )
	{
		appendProcedure( anElement );
	}
	else
	{
		appendMachine( anElement );
	}
}


/**
 * GETTER - SETTER
 * mOutgoingTransitions
 */
void CompositePart::appendOutgoingTransitionToEveryState(Machine * aGroupState)
{
	if( aGroupState->hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState->getBehavior();
		BehavioralPart::const_transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::const_transition_iterator itTransition;
		Transition * newTransition;

		CompositePart * aGroupCompositePart = aGroupState->getCompositePart();
		const_state_iterator itMachine = aGroupCompositePart->state_begin();
		const_state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask()) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition((itMachine), (itTransition));

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}


void CompositePart::appendOutgoingTransitionToSomeState(Machine * aGroupState)
{
	if( aGroupState->hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState->getBehavior();
		BehavioralPart::const_transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::const_transition_iterator itTransition;
		Transition * newTransition;

		const ListOfString & listofId = aGroupState->getGroupId();

		CompositePart * aGroupCompositePart = aGroupState->getCompositePart();
		const_state_iterator itMachine = aGroupCompositePart->state_begin();
		const_state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask())
				&& listofId.contains((itMachine)->getNameID()) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition((itMachine), (itTransition));

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}

void CompositePart::appendOutgoingTransitionToExceptState(Machine * aGroupState)
{
	if( aGroupState->hasOutgoingTransition() )
	{
		BehavioralPart * aGroupStateBehavior = aGroupState->getBehavior();
		BehavioralPart::const_transition_iterator endTransition =
				aGroupStateBehavior->outgoing_transition_end();
		BehavioralPart::const_transition_iterator itTransition;
		Transition * newTransition;

		const ListOfString & listofId = aGroupState->getGroupId();

		CompositePart * aGroupCompositePart = aGroupState->getCompositePart();
		const_state_iterator itMachine = aGroupCompositePart->state_begin();
		const_state_iterator endMachine = aGroupCompositePart->state_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (itMachine)->getSpecifier().isStateSimple()
				&& (not (itMachine)->getSpecifier().hasGroupMask())
				&& (not listofId.contains((itMachine)->getNameID())) )
			{
				itTransition = aGroupStateBehavior->outgoing_transition_begin();
				for( ; itTransition != endTransition ; ++itTransition )
				{
					newTransition = new Transition((itMachine), (itTransition));

					(itMachine)->getUniqBehaviorPart()->
							saveOutgoingTransition( newTransition );
				}
			}
		}
	}
}


void CompositePart::expandGroupStatemachine()
{
	const_state_iterator itMachine = state_begin();
	const_state_iterator endMachine = state_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (itMachine)->getSpecifier().hasGroupMask() )
		{
			if( (itMachine)->getSpecifier().isGroupEvery())
			{
				appendOutgoingTransitionToEveryState( (itMachine) );
			}
			else if( (itMachine)->getSpecifier().isGroupSome())
			{
				appendOutgoingTransitionToSomeState( (itMachine) );
			}
			else if( (itMachine)->getSpecifier().isGroupExcept() )
			{
				appendOutgoingTransitionToExceptState( (itMachine) );
			}
		}
	}
}


/**
 * Serialization
 */
void CompositePart::toStream(OutStream & os) const
{
	if( hasProcedure() )
	{
		os << TAB << "procedure:" << EOL_INCR_INDENT;
		const_procedure_iterator it = procedure_begin();
		const_procedure_iterator endIt = procedure_end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(os);
			os << EOL;
		}
		os << DECR_INDENT;
	}

	if( hasState() )
	{
		const std::string & sequenceName = ( getContainerMachine()->
				getSpecifier().isComponentStatemachine() ?
						"region" : "statemachine" );

		os << TAB << "/*" << sequenceName << ": [" << EOL_INCR_INDENT
				<< str_header( mStates ) << DECR_INDENT_TAB
				<< "] // end " << sequenceName << "*/" << EOL2_FLUSH;

//		os << TAB << sequenceName << ":" << EOL_INCR_INDENT;
//
//		const_state_iterator it = state_begin();
//		const_state_iterator endIt = state_end();
//		for( ; it != endIt ; ++it )
//		{
//			(it)->toStream(os);
//			os << EOL;
//		}
//		os << DECR_INDENT;
	}

	if( hasMachine() )
	{
		os << TAB << getNameID() /*composite*/ << ":" << EOL_INCR_INDENT;

		const_machine_iterator it = machine_begin();
		const_machine_iterator endIt = machine_end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(os);
			os << EOL;
		}
		os << DECR_INDENT;
	}

	if( hasInstanceStatic() )
	{
		os << TAB << "/*instance: [" << EOL_INCR_INDENT
				<< str_header( mInstanceStatics ) << DECR_INDENT_TAB
				<< "] // end instance*/" << EOL2_FLUSH;

//		os << TAB << "instance:" << EOL_INCR_INDENT;
//
//		const_instance_iterator it = instance_begin();
//		const_instance_iterator endIt = instance_end();
//		for( ; it != endIt ; ++it )
//		{
//			(it)->toStream(os);
//		}
//		os << DECR_INDENT;
	}

	if( hasInstanceDynamic() )
	{
//		os << TAB << "/*#dynamic instance: [" << EOL_INCR_INDENT
//				<< str_header( mInstanceDynamics ) << DECR_INDENT_TAB
//				<< "] // end dynamic*/" << EOL2_FLUSH;

		os << TAB << "instance#dynamic:" << EOL_INCR_INDENT;
		const_machine_iterator it = instance_dynamic_begin();
		const_machine_iterator endIt = instance_dynamic_end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(os);
			os << EOL;
		}
		os << DECR_INDENT;
	}

	os << std::flush;
}


} /* namespace sep */
