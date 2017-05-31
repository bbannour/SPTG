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

#include "ExecutableQuery.h"

#include <collection/Collection.h>

#include <common/NamedElement.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{


/**
 * GETTER
 * List of all RUNTIME Executable Element
 */
void ExecutableQuery::getRuntimeExecutable(InstanceOfMachine * aMachine,
		Collection< ExecutableForm * > & listOfExecutable)
{
	listOfExecutable.add_union( aMachine->getExecutable() );

	TableOfSymbol::const_iterator it;
	TableOfSymbol::const_iterator itEnd;

	it = aMachine->getExecutable()->instance_model_begin();
	itEnd = aMachine->getExecutable()->instance_model_end();
	for( ; it != itEnd ; ++it )
	{
		getRuntimeExecutable((*it).rawMachine(), listOfExecutable);
	}

	it = aMachine->getExecutable()->instance_static_begin();
	itEnd = aMachine->getExecutable()->instance_static_end();
	for( ; it != itEnd ; ++it )
	{
		getRuntimeExecutable((*it).rawMachine(), listOfExecutable);
	}
}



/**
 * SEARCH
 * AvmTransition
 */
const BF & ExecutableQuery::getTransitionByAstElement(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const BF & foundTransition =
				(itExec)->getTransitionByAstElement(astElement);
		if( foundTransition.valid() )
		{
			return( foundTransition );
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableQuery::getTransition(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const BF & foundTransition =
				(itExec)->getTransition(aFullyQualifiedNameID);

		if( foundTransition.valid() )
		{
			return( foundTransition );
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableQuery::getTransitionByNameID(
		const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const BF & foundTransition = (itExec)->getTransitionByNameID( aNameID );
		if( foundTransition.valid() )
		{
			return( foundTransition );
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutableQuery::getTransitionByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const BF & foundTransition =
				(itExec)->getTransitionByQualifiedNameID(aQualifiedNameID);

		if( foundTransition.valid() )
		{
			return( foundTransition );
		}
	}

	return( BF::REF_NULL );
}


/**
 * SEARCH
 * AvmProgram
 */
const BF & ExecutableQuery::getProgram(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const BF & foundProgram = (itExec)->getProgram(aFullyQualifiedNameID);

		if( foundProgram.valid() )
		{
			return( foundProgram );
		}
	}

	return( BF::REF_NULL );
}



/**
 * SEARCH
 * AvmProgram
 * ExecutableForm
 */
const BF & ExecutableQuery::getExecutableOrProgram(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( NamedElement::compareLocation(
				itExec->getFullyQualifiedNameID(), aFullyQualifiedNameID) )
		{
			return( (*itExec) );
		}
		else
		{
			{
				const BF & foundTransition =
						itExec->getTransition(aFullyQualifiedNameID);

				if( foundTransition.valid() )
				{
					return( foundTransition );
				}
			}
			{
				const BF & foundProgram =
						itExec->getProgram(aFullyQualifiedNameID);

				if( foundProgram.valid() )
				{
					return( foundProgram );
				}
			}
		}
	}

	return( BF::REF_NULL );
}


// Getter by AST-Element
const BF & ExecutableQuery::getExecutableOrProgram(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		if( itExec->isAstElement( astElement ) )
		{
			return( (*itExec) );
		}
		else
		{
			{
				const BF & foundTransition =
						itExec->getTransitionByAstElement(astElement);

				if( foundTransition.valid() )
				{
					return( foundTransition );
				}
			}
			{
				const BF & foundProgram =
						itExec->getProgramByAstElement(astElement);
				if( foundProgram.valid() )
				{
					return( foundProgram );
				}
			}
		}
	}

	return( BF::REF_NULL );
}


/**
 * SEARCH
 * InstanceOfBuffer
 */
const Symbol & ExecutableQuery::getBuffer(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getBuffer().getByFQNameID( aFullyQualifiedNameID );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getBufferByNameID(
		const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getBuffer().getByNameID( aNameID );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getBufferByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getBuffer().getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getBufferByAstElement(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getBuffer().getByAstElement(astElement);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}




/**
 * SEARCH
 * InstanceOfData
 */
const BF & ExecutableQuery::getDataByNameID(const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		{
			const BF & foundElement =
					(itExec)->getAllData().getByNameID( aNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement =
					(itExec)->getConstData().getByNameID( aNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}

const BF & ExecutableQuery::getDataByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		{
			const BF & foundElement = (itExec)->getAllData().
					getByQualifiedNameID(aQualifiedNameID);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement = (itExec)->getConstData().
					getByQualifiedNameID(aQualifiedNameID);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableQuery::getData(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		{
			const BF & foundElement =
				(itExec)->getAllData().getByFQNameID( aFullyQualifiedNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement =
				(itExec)->getConstData().getByFQNameID( aFullyQualifiedNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableQuery::getDataByAstElement(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		{
			const BF & foundElement =
					(itExec)->getAllData().getByAstElement(astElement);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement =
					(itExec)->getConstData().getByAstElement(astElement);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}


/**
 * SEARCH
 * Symbol as InstanceOfPort
 * by ID
 */
const Symbol & ExecutableQuery::getPortByNameID(const std::string & aNameID,
		Modifier::DIRECTION_KIND ioDirection) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement = (itExec)->getPort().getByNameID(aNameID);

		if( foundElement.valid()
			&& foundElement.getModifier().isDirectionKind(ioDirection) )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getPortByNameID(
		const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement = (itExec)->getPort().getByNameID(aNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}



avm_size_t ExecutableQuery::getPortByNameID(
		const std::string & aNameID, ListOfSymbol & listofPort,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	avm_size_t count = 0;

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		count += (itExec)->getPort().getByNameID(aNameID, listofPort);
	}

	ListOfSymbol::iterator itPort  = listofPort.begin();
	ListOfSymbol::iterator endPort = listofPort.end();
	for( ; itPort != endPort ; )
	{
		if( (*itPort).getModifier().
				isnotDirectionKind(ioDirection, isStrongly) )
		{
			itPort = listofPort.erase(itPort);
		}
		else
		{
			++itPort;
		}
	}


	return( count );
}


avm_size_t ExecutableQuery::getPortByNameID(
		const std::string & aNameID, ListOfSymbol & listofPort) const
{
	avm_size_t count = 0;

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		count += (itExec)->getPort().getByNameID(aNameID, listofPort);
	}

	return( count );
}


/**
 * SEARCH
 * Symbol as InstanceOfPort
 * by [ [ FULLY ] QUALIFIED ] NAME ID
 */
const Symbol & ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getPort().getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid()
			&& foundElement.getModifier().
					isDirectionKind(ioDirection, isStrongly) )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


avm_size_t ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID, ListOfSymbol & listofPort,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	avm_size_t count = 0;

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		count += (itExec)->getPort().
				getByQualifiedNameID(aQualifiedNameID, listofPort);
	}

	ListOfSymbol::iterator itPort  = listofPort.begin();
	ListOfSymbol::iterator endPort = listofPort.end();
	for( ; itPort != endPort ; )
	{
		if( (*itPort).getModifier().isnotDirectionKind(ioDirection, isStrongly) )
		{
			itPort = listofPort.erase(itPort);
		}
		else
		{
			++itPort;
		}
	}


	return( count );
}


avm_size_t ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID, ListOfSymbol & listofPort) const
{
	avm_size_t count = 0;

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		count += (itExec)->getPort().
				getByQualifiedNameID(aQualifiedNameID, listofPort);
	}

	return( count );
}


const Symbol & ExecutableQuery::getPort(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getPort().getByFQNameID( aFullyQualifiedNameID );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemPort(const ExecutableForm * anExecutable,
		const std::string & aFullyQualifiedNameID)
{
	for( ; anExecutable != NULL ;
			anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundElement =
				anExecutable->getPort().getByFQNameID( aFullyQualifiedNameID );
		if( foundElement.valid() )
		{
			return foundElement;
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getPortByAstElement(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getPort().getByAstElement(astElement);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getSemPortByAstElement(
		const ExecutableForm * anExecutable, const ObjectElement * astElement)
{
	for( ; anExecutable != NULL ;
			anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundElement =
				anExecutable->getPort().getByAstElement( astElement );
		if( foundElement.valid() )
		{
			return foundElement;
		}
	}

	return( Symbol::REF_NULL );
}


/**
 * SEARCH
 * InstanceOfChannel
 */
const Symbol & ExecutableQuery::getChannel(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getChannel().getByAstElement(astElement);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


/**
 * SEARCH
 * InstanceOfMachine
 */
const Symbol & ExecutableQuery::getMachine(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aFullyQualifiedNameID) const
{
	// STRICT:> compare LOCATOR & LOCATION [true:- retry only only LOCATION]
	if( getSystem().fqnEquals( aFullyQualifiedNameID , true ) )
	{
		return( getSystem().getSystemInstance() );
	}

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement = (itExec)->getInstanceByDesign(
				aDesign ).getByFQNameID( aFullyQualifiedNameID );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getMachineByNameID(
		Specifier::DESIGN_KIND aDesign, const std::string & aNamleID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getInstanceByDesign(aDesign).getByNameID(aNamleID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getMachineByQualifiedNameID(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement = (itExec)->getInstanceByDesign(aDesign).
				getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


InstanceOfMachine * ExecutableQuery::rawMachineByNameID(
		Specifier::DESIGN_KIND aDesign, const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		InstanceOfMachine * foundElement =
				(itExec)->getInstanceByDesign(
						aDesign ).getByNameID(aNameID).rawMachine();

		if( foundElement != NULL )
		{
			return( foundElement );
		}
	}

	return( NULL );
}

InstanceOfMachine * ExecutableQuery::rawMachineByQualifiedNameID(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		InstanceOfMachine * foundElement = (itExec)->getInstanceByDesign(
				aDesign ).getByQualifiedNameID(aQualifiedNameID).rawMachine();

		if( foundElement != NULL )
		{
			return( foundElement );
		}
	}

	return( NULL );
}


const Symbol & ExecutableQuery::getMachineByAstElement(
		Specifier::DESIGN_KIND aDesign, const ObjectElement * astElement) const
{
	if( getSystem().rawSystemInstance()->isAstElement( astElement ) )
	{
		return( getSystem().getSystemInstance() );
	}

	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
			(itExec)->getInstanceByDesign(aDesign).getByAstElement(astElement);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


/**
 * SEARCH
 * Machine
 */
const BF & ExecutableQuery::searchMachine(
		Specifier::DESIGN_KIND aDesign, const std::string & aQualifiedNameID )
{
	std::string::size_type pos = aQualifiedNameID.find("->");

	if( pos != std::string::npos )
	{
		std::string mid = aQualifiedNameID.substr(0, pos);
		std::string obj = aQualifiedNameID.substr(pos + 2);

		InstanceOfMachine * mainMachine = NULL;

		if( mid.find('.') == std::string::npos )
		{
			mainMachine = rawMachineByNameID(aDesign, mid);
		}
		else
		{
			mainMachine = rawMachineByQualifiedNameID(aDesign, mid);
		}

		if( mainMachine != NULL )
		{
			if( obj != "[*]" )
			{
				const BF & machine = mainMachine->getExecutable()->
						getInstanceByDesign( aDesign ).getByNameID( obj );
				if( machine.valid() )
				{
					return( machine );
				}

			}
		}
		else
		{
			const BF & machine =
					getMachineByQualifiedNameID(aDesign, mid + "." + obj);
			if( machine.valid() )
			{
				return( machine );
			}
		}
	}
	else
	{
		if( aQualifiedNameID.find('.') == std::string::npos )
		{
			const BF & machine = getMachineByNameID(aDesign, aQualifiedNameID);
			if( machine.valid() )
			{
				return( machine );
			}
		}
		else
		{
			const BF & machine =
					getMachineByQualifiedNameID(aDesign, aQualifiedNameID);
			if( machine.valid() )
			{
				return( machine );
			}
		}
	}

	return( BF::REF_NULL );
}


/**
 * SEARCH
 * for Machine Instance Model
 */
const Symbol & ExecutableQuery::getInstanceModel(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getByAstInstanceModel( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceModel(
		const ExecutableForm * anExecutable,
		const ObjectElement * astElement) const
{
	for( ; anExecutable != NULL ;
			anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExecutable->getByAstInstanceModel( astElement );
		if( foundInstance.valid() && foundInstance.machine().isnotThis() )
		{
			return( foundInstance );
		}
	}

	return( getInstanceModel( astElement ) );
}


/**
 * SEARCH
 * for Machine Instance Static
 */
const Symbol & ExecutableQuery::getInstanceStatic(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getByAstInstanceStatic( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceStatic(
		const ExecutableForm * anExecutable,
		const ObjectElement * astElement) const
{
	for( ; anExecutable != NULL ;
			anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExecutable->getByAstInstanceStatic( astElement );
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( getInstanceStatic( astElement ) );
}


/**
 * SEARCH
 * for Machine Instance Dynamic
 */
const Symbol & ExecutableQuery::getInstanceDynamic(
		const ObjectElement * astElement) const
{
	// REVERSE because machines are insert after children
	const_exec_iterator itExec  = getSystem().getExecutables().begin();
	const_exec_iterator endExec  = getSystem().getExecutables().end();
	for( ; itExec != endExec ; ++itExec )
	{
		const Symbol & foundElement =
				(itExec)->getByAstInstanceDynamic( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceDynamic(
		const ExecutableForm * anExecutable,
		const ObjectElement * astElement) const
{
	for( ; anExecutable != NULL ; anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundInstance =
				anExecutable->getByAstInstanceDynamic( astElement );
		if( foundInstance.valid() )
		{
			return( foundInstance );
		}
	}

	return( getInstanceDynamic( astElement ) );
}


/**
 * SEARCH
 * any Instance
 */
const BF & ExecutableQuery::getInstanceByAstElement(
		const ObjectElement * astElement) const
{
	if( getSystem().rawSystemInstance()->isAstElement( astElement ) )
	{
		return( getSystem().getSystemInstance() );
	}

	{
		const BF & foundElement = getDataByAstElement(astElement);
		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}
	{
		const Symbol & foundElement = getPortByAstElement(astElement);
		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}
	{
		const Symbol & foundElement = getMachineByAstElement(
				Specifier::DESIGN_INSTANCE_KIND, astElement);
		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}
	{
		const Symbol & foundElement = getBufferByAstElement(astElement);
		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( BF::REF_NULL );
}


} /* namespace sep */
