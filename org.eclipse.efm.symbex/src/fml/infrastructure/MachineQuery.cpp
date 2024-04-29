/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 mars 2017
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Machine.h"

#include <fml/infrastructure/BehavioralPart.h>
#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>
#include <fml/infrastructure/System.h>


namespace sep
{


/**
 * GETTER for PARSER / COMPILER
 * any Property Element
 */
const BF & MachineQuery::getPropertyByNameID(const std::string & aNameID) const
{
	return( getPropertyPart().getObjectByNameID(aNameID) );
}

const BF & MachineQuery::getrecPropertyByNameID(const std::string & aNameID) const
{
	const BF & property = getPropertyByNameID(aNameID);
	if( property.valid() )
	{
		return( property );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & property = (itMachine)->getPropertyByNameID(aNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemPropertyByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	const BF & property = machine->getPropertyByNameID(aNameID);
	if( property.valid() )
	{
		return( property );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & property = machine->getPropertyByNameID(aNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}


const BF & MachineQuery::getPropertyByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().
			getObjectByQualifiedNameID(aQualifiedNameID) );
}

const BF & MachineQuery::getrecPropertyByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const BF & property = getPropertyByQualifiedNameID(aQualifiedNameID);
	if( property.valid() )
	{
		return( property );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & property =
				(itMachine)->getPropertyByQualifiedNameID(aQualifiedNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemPropertyByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & property = machine->getPropertyByQualifiedNameID(aQualifiedNameID);
	if( property.valid() )
	{
		return( property );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & property =
				machine->getPropertyByQualifiedNameID(aQualifiedNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER for PARSER / COMPILER
 * Variable
 */
const BF & MachineQuery::getVariable(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getVariable(aQualifiedNameID) );
}

const BF & MachineQuery::getrecVariable(
		const std::string & aQualifiedNameID) const
{
	const BF & var = getVariable(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecVariable(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemVariable(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getVariable(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getVariable(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


std::vector< std::string> MachineQuery::getVariableNames() const
{
	return( getPropertyPart().getVariables().getVectorOfAllNameID() );
}


/*
 * TYPEDEF VARIABLE
 * as ENUMERATION | STRUCTURE
 */

const BF & MachineQuery::getDataType(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getDataType(aQualifiedNameID) );
}

const BF & MachineQuery::getrecDataType(
		const std::string & aQualifiedNameID) const
{
	const BF & var = getDataType(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecDataType(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemDataType(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getDataType(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getDataType(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER for PARSER / COMPILER
 * Buffer
 */
const BF & MachineQuery::getBuffer(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getBuffer(aQualifiedNameID) );
}

const BF & MachineQuery::getrecBuffer(const std::string & aQualifiedNameID) const
{
	const BF & var = getBuffer(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecBuffer(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemBuffer(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getBuffer(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getBuffer(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


std::vector< std::string> MachineQuery::getBufferNames() const
{
	return( getPropertyPart().getBuffers().getVectorOfAllNameID() );
}


/**
 * GETTER for PARSER / COMPILER
 * Channel
 */
const BF & MachineQuery::getChannel(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getChannel(aQualifiedNameID) );
}

const BF & MachineQuery::getrecChannel(
		const std::string & aQualifiedNameID) const
{
	const BF & var = getChannel(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecChannel(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemChannel(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getChannel(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getChannel(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


std::vector< std::string> MachineQuery::getChannelNames() const
{
	return( getPropertyPart().getChannels().getVectorOfAllNameID() );
}


/**
 * GETTER for PARSER / COMPILER
 * Port
 */
const BF & MachineQuery::getPort(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getPort(aQualifiedNameID) );
}

const BF & MachineQuery::getrecPort(const std::string & aQualifiedNameID) const
{
	const BF & var = getPort(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecPort(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemPort(const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getPort(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getPort(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


std::vector< std::string> MachineQuery::getPortNames() const
{
	return( getPropertyPart().getPorts().getVectorOfAllNameID() );
}


/**
 * GETTER for PARSER / COMPILER
 * Signal
 */
const BF & MachineQuery::getSignal(const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getSignal(aQualifiedNameID) );
}

const BF & MachineQuery::getrecSignal(
		const std::string & aQualifiedNameID) const
{
	const BF & var = getSignal(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemSignal(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & var = machine->getSignal(aQualifiedNameID);
	if( var.valid() )
	{
		return( var );
	}
	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


std::vector< std::string> MachineQuery::getSignalNames() const
{
	return( getPropertyPart().getSignals().getVectorOfAllNameID() );
}


/**
 * GETTER for PARSER / COMPILER
 * Port / Signal
 */
const BF & MachineQuery::getPortSignal(
		const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().getPortSignal(aQualifiedNameID) );
}

const BF & MachineQuery::getrecPortSignal(
		const std::string & aQualifiedNameID) const
{
	{
		const BF & var = getPortSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & var = (itMachine)->getrecPortSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemPortSignal(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	{
		const BF & var = machine->getPortSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}
	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & var = machine->getPortSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER for PARSER / COMPILER
 * any Behavior Element
 */
const BF & MachineQuery::getBehaviorByNameID(const std::string & aNameID) const
{
	if( hasBehaviorPart() )
	{
		return( getBehaviorPart()->getObjectByNameID(aNameID) );
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getrecBehaviorByNameID(const std::string & aNameID) const
{
	const BF & behavior = getBehaviorByNameID(aNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & behavior = (itMachine)->getBehaviorByNameID(aNameID);
		if( behavior.valid() )
		{
			return( behavior );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemBehaviorByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	const BF & behavior = machine->getBehaviorByNameID(aNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & behavior = machine->getBehaviorByNameID(aNameID);
		if( behavior.valid() )
		{
			return( behavior );
		}
	}

	return( BF::REF_NULL );
}


const BF & MachineQuery::getBehaviorByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	if( hasBehaviorPart() )
	{
		return( getBehaviorPart()->getObjectByQualifiedNameID(aQualifiedNameID) );
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getrecBehaviorByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const BF & behavior = getBehaviorByQualifiedNameID(aQualifiedNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & behavior =
				(itMachine)->getBehaviorByQualifiedNameID(aQualifiedNameID);
		if( behavior.valid() )
		{
			return( behavior );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemBehaviorByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & behavior = machine->getBehaviorByQualifiedNameID(aQualifiedNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & behavior =
				machine->getBehaviorByQualifiedNameID(aQualifiedNameID);
		if( behavior.valid() )
		{
			return( behavior );
		}
	}

	return( BF::REF_NULL );
}


/**
 * GETTER for PARSER / COMPILER
 * Transition
 */
std::vector< std::string> MachineQuery::getTransitionNames() const
{
	if( hasBehaviorPart() )
	{
		return( getBehaviorPart()->getOutgoingTransitions().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}


/**
 * GETTER for PARSER / COMPILER
 * Routine
 */
Routine * MachineQuery::rawRoutineByNameID(const std::string & aNameID) const
{
	return( (not hasBehaviorPart()) ? nullptr :
			getBehaviorPart()->rawRoutineByNameID(aNameID) );
}

Routine * MachineQuery::rawsemRoutineByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	Routine * routine = machine->rawRoutineByNameID(aNameID);

	while( (routine == nullptr) && machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		routine = machine->rawRoutineByNameID(aNameID);
	}

	return( routine );
}


std::vector< std::string> MachineQuery::getRoutineNames() const
{
	if( hasBehaviorPart() )
	{
		return( getBehaviorPart()->getRoutines().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}


/**
 * GETTER for PARSER / COMPILER
 * Procedure
 */
Machine * MachineQuery::rawProcedureByNameID(const std::string & aNameID) const
{
	return( (getCompositePart() == nullptr) ? nullptr :
			getCompositePart()->rawProcedureByNameID(aNameID) );
}

Machine * MachineQuery::rawsemProcedureByNameID(
		const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	Machine * procedure = machine->rawProcedureByNameID(aNameID);

	while( (procedure == nullptr) && machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		procedure = machine->rawProcedureByNameID(aNameID);
	}

	return( procedure );
}


std::vector< std::string> MachineQuery::getProcedureNames() const
{
	if( hasCompositePart() )
	{
		return( getCompositePart()->getProcedures().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}


/**
 * GETTER for PARSER / COMPILER
 * Machine
 */
Machine * MachineQuery::getMachineByNameID(const std::string & aNameID) const
{
	if( thisMachine()->getNameID() == aNameID )
	{
		return( const_cast< Machine * >( thisMachine() ) );
	}

	return( (getCompositePart() == nullptr) ? nullptr :
			getCompositePart()->rawMachineByNameID(aNameID) );
}


Machine * MachineQuery::getsemMachineByNameID(const std::string & aNameID) const
{
	Machine * machine = const_cast< Machine * >( thisMachine() );
	Machine * sm = machine->getMachineByNameID(aNameID);

	while( (sm == nullptr) &&  machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		sm = machine->getMachineByNameID(aNameID);
	}

	return( sm );
}


Machine * MachineQuery::getMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = getCompositePart()->
			getMachines().rawByQualifiedNameID(aQualifiedNameID);
	if( machine != nullptr )
	{
		return( machine );
	}

	if( thisMachine()->fqnEquals( aQualifiedNameID , false ) )
	{
		return( const_cast< Machine * >( thisMachine() ) );
	}

	return( machine );
}

Machine * MachineQuery::getrecMachine(const std::string & aQualifiedNameID,
		Machine * ignoreChildMachine) const
{
	Machine * machine = getMachine(aQualifiedNameID);
	if( machine != nullptr )
	{
		return( machine );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( itMachine->isNTEQ( ignoreChildMachine ) )
		{
			machine = (itMachine)->getrecMachine(aQualifiedNameID);
			if( machine != nullptr )
			{
				return( machine );
			}
		}
	}

	return( machine );
}

Machine * MachineQuery::getsemMachine(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	Machine * sm = machine->getMachine(aQualifiedNameID);

	while( (sm == nullptr) && machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		sm = machine->getMachine(aQualifiedNameID);
	}

	return( sm );
}



Machine * MachineQuery::getsemMachine(
		const std::vector< std::string > & aQualifiedNameID) const
{
	std::vector< std::string >::const_iterator it = aQualifiedNameID.begin();
	std::vector< std::string >::const_iterator endIt = aQualifiedNameID.end();

	Machine * sm = thisMachine()->getsemMachineByNameID(*it);

	for( ++it; (sm != nullptr) && (it != endIt) ; ++it)
	{
		sm = sm->getMachineByNameID(*it);
	}

	return( sm );
}



Machine * MachineQuery::getExecutableMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = getCompositePart()->
			rawExecutableMachineByQualifiedNameID(aQualifiedNameID);
	if( machine != nullptr )
	{
		return( machine );
	}

	return( machine );
}

Machine * MachineQuery::getrecExecutableMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = getExecutableMachine(aQualifiedNameID);
	if( machine != nullptr )
	{
		return( machine );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		machine = (itMachine)->getrecExecutableMachine(aQualifiedNameID);
		if( machine != nullptr )
		{
			return( machine );
		}
	}

	return( machine );
}

Machine * MachineQuery::getsemExecutableMachine(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	Machine * sm = machine->getExecutableMachine(aQualifiedNameID);

	while( (sm == nullptr) && machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		sm = machine->getExecutableMachine(aQualifiedNameID);
	}

	return( sm );
}


Machine * MachineQuery::getSelfExecutableMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = const_cast< Machine * >( thisMachine() );
	while( machine != nullptr )
	{
		if( machine->fqnEndsWith(aQualifiedNameID) )
		{
			return( machine );
		}

		machine = machine->getContainer()->to_ptr< Machine >();
	}

	return( machine );
}

System * MachineQuery::getContainerSystem() const
{
	Machine * machine = const_cast< Machine * >( thisMachine() );
	while( (machine != nullptr) && machine->isnot< System >() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();
	}

	return( (machine != nullptr) ? machine->to_ptr< System >() : nullptr );
}


std::vector< std::string> MachineQuery::getMachineNames() const
{
	if( hasCompositePart() )
	{
		return( getCompositePart()->getMachines().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}

std::vector< std::string> MachineQuery::getInstanceNames() const
{
	if( hasCompositePart() )
	{
		return( getCompositePart()->getInstanceStatics().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}

std::vector< std::string> MachineQuery::getStateNames() const
{
	if( hasCompositePart() )
	{
		return( getCompositePart()->getStates().getVectorOfAllNameID() );
	}
	else
	{
		return( std::vector< std::string>() );
	}
}


/**
 * GETTER for PARSER / COMPILER
 * any Object Element
 */
const BF & MachineQuery::getObjectByNameID(const std::string & aNameID) const
{
	const BF & property = getPropertyByNameID(aNameID);
	if( property.valid() )
	{
		return( property );
	}

	const BF & behavior = getBehaviorByNameID(aNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getrecObjectByNameID(const std::string & aNameID) const
{
	const BF & property = getObjectByNameID(aNameID);
	if( property.valid() )
	{
		return( property );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & property = (itMachine)->getObjectByNameID(aNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemObjectByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	const BF & property = machine->getObjectByNameID(aNameID);
	if( property.valid() )
	{
		return( property );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & property = machine->getObjectByNameID(aNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getObjectByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const BF & property = getPropertyByQualifiedNameID(aQualifiedNameID);
	if( property.valid() )
	{
		return( property );
	}

	const BF & behavior = getBehaviorByQualifiedNameID(aQualifiedNameID);
	if( behavior.valid() )
	{
		return( behavior );
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getrecObjectByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const BF & property = getObjectByQualifiedNameID(aQualifiedNameID);
	if( property.valid() )
	{
		return( property );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & property =
				(itMachine)->getObjectByQualifiedNameID(aQualifiedNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemObjectByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & property = machine->getObjectByQualifiedNameID(aQualifiedNameID);
	if( property.valid() )
	{
		return( property );
	}

	while( machine->isContainerMachine() )
	{
		machine = machine->getContainer()->to_ptr< Machine >();

		const BF & property =
				machine->getObjectByQualifiedNameID(aQualifiedNameID);
		if( property.valid() )
		{
			return( property );
		}
	}

	return( BF::REF_NULL );
}


} /* namespace sep */
