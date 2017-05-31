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


namespace sep
{


/**
 * GETTER for PARSER / COMPILER
 * any Object Element
 */
const BF & MachineQuery::getPropertyByNameID(const std::string & aNameID) const
{
	return( getPropertyPart().getPropertyByNameID(aNameID) );
}

const BF & MachineQuery::getrecFormByNameID(const std::string & aNameID) const
{
	const BF & form = getPropertyByNameID(aNameID);
	if( form.valid() )
	{
		return( form );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & form = (itMachine)->getPropertyByNameID(aNameID);
		if( form.valid() )
		{
			return( form );
		}
	}

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemFormByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	const BF & form = machine->getPropertyByNameID(aNameID);
	if( form.valid() )
	{
		return( form );
	}

	while( machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & form = machine->getPropertyByNameID(aNameID);
		if( form.valid() )
		{
			return( form );
		}
	}

	return( BF::REF_NULL );
}


const BF & MachineQuery::getPropertyByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	return( getPropertyPart().
			getPropertyByQualifiedNameID(aQualifiedNameID) );
}

const BF & MachineQuery::getrecFormByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const BF & form = getPropertyByQualifiedNameID(aQualifiedNameID);
	if( form.valid() )
	{
		return( form );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		const BF & form =
				(itMachine)->getPropertyByQualifiedNameID(aQualifiedNameID);
		if( form.valid() )
		{
			return( form );
		}
	}

	return( BF::REF_NULL );

	return( BF::REF_NULL );
}

const BF & MachineQuery::getsemFormByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	const BF & form = machine->getPropertyByQualifiedNameID(aQualifiedNameID);
	if( form.valid() )
	{
		return( form );
	}

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & form =
				machine->getPropertyByQualifiedNameID(aQualifiedNameID);
		if( form.valid() )
		{
			return( form );
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

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & var = machine->getVariable(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
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

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

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

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & var = machine->getBuffer(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
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

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & var = machine->getChannel(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
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

	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & var = machine->getPort(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
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
	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		const BF & var = machine->getSignal(aQualifiedNameID);
		if( var.valid() )
		{
			return( var );
		}
	}

	return( BF::REF_NULL );
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
	while( machine->hasContainer()
			&& machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

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
 * Routine
 */
Routine * MachineQuery::rawRoutineByNameID(const std::string & aNameID) const
{
	return( (not hasBehaviorPart()) ? NULL :
			getBehaviorPart()->rawRoutineByNameID(aNameID) );
}

Routine * MachineQuery::rawsemRoutineByNameID(const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	Routine * routine = machine->rawRoutineByNameID(aNameID);

	while( (routine == NULL) && machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		routine = machine->rawRoutineByNameID(aNameID);
	}

	return( routine );
}


/**
 * GETTER for PARSER / COMPILER
 * Procedure
 */
Machine * MachineQuery::rawProcedureByNameID(const std::string & aNameID) const
{
	return( (getCompositePart() == NULL) ? NULL :
			getCompositePart()->rawProcedureByNameID(aNameID) );
}

Machine * MachineQuery::rawsemProcedureByNameID(
		const std::string & aNameID) const
{
	const Machine * machine = thisMachine();

	Machine * procedure = machine->rawProcedureByNameID(aNameID);

	while( (procedure == NULL) && machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		procedure = machine->rawProcedureByNameID(aNameID);
	}

	return( procedure );
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

	return( (getCompositePart() == NULL) ? NULL :
			getCompositePart()->rawMachineByNameID(aNameID) );
}


Machine * MachineQuery::getsemMachineByNameID(const std::string & aNameID) const
{
	Machine * machine = const_cast< Machine * >( thisMachine() );
	Machine * sm = machine->getMachineByNameID(aNameID);

	while( (sm == NULL) &&  machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		sm = machine->getMachineByNameID(aNameID);
	}

	return( sm );
}


Machine * MachineQuery::getMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = getCompositePart()->
			getMachines().rawByQualifiedNameID(aQualifiedNameID);
	if( machine != NULL )
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
	Machine * machine = NULL;

	if( (machine = getMachine(aQualifiedNameID)) != NULL )
	{
		return( machine );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( ((itMachine) != ignoreChildMachine) &&
			((machine = (itMachine)->getrecMachine(aQualifiedNameID)) != NULL) )
		{
			return( machine );
		}
	}

	return( machine );
}

Machine * MachineQuery::getsemMachine(
		const std::string & aQualifiedNameID) const
{
	const Machine * machine = thisMachine();

	Machine * sm = machine->getMachine(aQualifiedNameID);

	while( (sm == NULL) && machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

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

	for( ++it; (sm != NULL) && (it != endIt) ; ++it)
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
	if( machine != NULL )
	{
		return( machine );
	}

	return( machine );
}

Machine * MachineQuery::getrecExecutableMachine(
		const std::string & aQualifiedNameID) const
{
	Machine * machine = NULL;

	if( (machine = getExecutableMachine(aQualifiedNameID)) != NULL )
	{
		return( machine );
	}

	CompositePart::const_machine_iterator itMachine =
			getCompositePart()->machine_begin();
	CompositePart::const_machine_iterator endMachine =
			getCompositePart()->machine_end();
	for( ; itMachine != endMachine ; ++itMachine )
	{
		if( (machine = (itMachine)->getrecExecutableMachine(aQualifiedNameID)) != NULL )
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

	while( (sm == NULL) && machine->hasContainer() &&
			machine->getContainer()->is< Machine >() )
	{
		machine = machine->getContainer()->to< Machine >();

		sm = machine->getExecutableMachine(aQualifiedNameID);
	}

	return( sm );
}



} /* namespace sep */
