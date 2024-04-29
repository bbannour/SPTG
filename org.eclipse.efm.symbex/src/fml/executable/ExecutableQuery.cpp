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
		Collection< const ExecutableForm * > & listOfExecutable)
{
	listOfExecutable.add_unique( aMachine->getExecutable() );

	TableOfSymbol::const_iterator it;
	TableOfSymbol::const_iterator itEnd;

	it = aMachine->refExecutable().instance_model_begin();
	itEnd = aMachine->refExecutable().instance_model_end();
	for( ; it != itEnd ; ++it )
	{
		getRuntimeExecutable((*it).rawMachine(), listOfExecutable);
	}

	it = aMachine->refExecutable().instance_static_begin();
	itEnd = aMachine->refExecutable().instance_static_end();
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
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const BF & foundTransition =
			itExec.to< ExecutableForm >().getTransitionByAstElement(astElement);
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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const BF & foundTransition = itExec.to< ExecutableForm >().
				getTransition(aFullyQualifiedNameID, true);

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const BF & foundTransition =
				itExec.to< ExecutableForm >().getTransitionByNameID( aNameID );
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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const BF & foundTransition = itExec.to< ExecutableForm >().
				getTransitionByQualifiedNameID(aQualifiedNameID);

		if( foundTransition.valid() )
		{
			return( foundTransition );
		}
	}

	return( BF::REF_NULL );
}


std::size_t ExecutableQuery::getTransitionByID(
		const ExecutableForm & anExecutable,
		const std::string & anID, BFList & listofTransition) const
{
	std::string::size_type pos = anID.find('.');

	const BF & foundTransition = (pos == std::string::npos)
			? anExecutable.getTransitionByNameID( anID )
			: getTransition( NamedElement::makeFullyQualifiedNameID(
					anExecutable.getFullyQualifiedNameID(), anID, false) );

	if( foundTransition.valid() )
	{
		listofTransition.append(foundTransition);

		return( listofTransition.size() );
	}
	else
	{
		return( getTransitionByREGEX(
			NamedElement::makeFullyRegexQualifiedNameID(
				anExecutable.getFullyQualifiedNameID(), anID, false),
				listofTransition) );
	}
}

// REGEX
std::size_t ExecutableQuery::getTransitionByREGEX(
		const std::string & aRedexID, BFList & listofTransition) const
{
	std::size_t count = 0;

	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getTransition().
				getByQualifiedNameREGEX(aRedexID, listofTransition);
	}

	return count;
}


std::size_t ExecutableQuery::getTransitionByNameREGEX(
		const ExecutableForm & anExecutable,
		const std::string & aRedexID, BFList & listofTransition) const
{
	std::size_t count = anExecutable.getTransition().
			getByNameREGEX(aRedexID, listofTransition);

	for( const auto & itModel : anExecutable.getInstanceStatic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getTransitionByNameREGEX(
					itModel.getExecutable(), aRedexID, listofTransition );
		}
	}

	for( const auto & itModel : anExecutable.getInstanceDynamic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getTransitionByNameREGEX(
					itModel.getExecutable(), aRedexID, listofTransition );
		}
	}

	return count;
}


/**
 * SEARCH
 * AvmProgram
 */
const BF & ExecutableQuery::getProgram(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const BF & foundProgram =
				itExec.to< ExecutableForm >().getProgram(aFullyQualifiedNameID);

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		if( itExec.to< ExecutableForm >().isLocationID(aFullyQualifiedNameID) )
		{
			return( itExec );
		}
		else
		{
			{
				const BF & foundTransition =
						itExec.to< ExecutableForm >().
						getTransition(aFullyQualifiedNameID);

				if( foundTransition.valid() )
				{
					return( foundTransition );
				}
			}
			{
				const BF & foundProgram =
						itExec.to< ExecutableForm >().
						getProgram(aFullyQualifiedNameID);

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
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		if( itExec.to< ExecutableForm >().isAstElement( astElement ) )
		{
			return( itExec );
		}
		else
		{
			{
				const BF & foundTransition =
						itExec.to< ExecutableForm >().
						getTransitionByAstElement(astElement);

				if( foundTransition.valid() )
				{
					return( foundTransition );
				}
			}
			{
				const BF & foundProgram =
						itExec.to< ExecutableForm >().
						getProgramByAstElement(astElement);
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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().getBuffer().
				getByFQNameID(aFullyQualifiedNameID, true);

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().getBuffer().getByNameID( aNameID );

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getBuffer().getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getBufferByAstElement(
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getBuffer().getByAstElement(astElement);

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
const BF & ExecutableQuery::getVariableByNameID(const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getAllVariables().getByNameID( aNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getConstVariable().getByNameID( aNameID );

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}

std::size_t ExecutableQuery::getVariableByNameID(
		const std::string & aNameID, BFList & listofVariable) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getAllVariables().
				getByNameID(aNameID, listofVariable);

		count += itExec.to< ExecutableForm >().getConstVariable().
				getByNameID(aNameID, listofVariable);
	}

	return( count );
}


const BF & ExecutableQuery::getVariableByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getAllVariables().getByQualifiedNameID(aQualifiedNameID);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getConstVariable().getByQualifiedNameID(aQualifiedNameID);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}

std::size_t ExecutableQuery::getVariableByQualifiedNameID(
		const std::string & aQualifiedNameID, BFList & listofVariable) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getAllVariables().
					getByQualifiedNameID(aQualifiedNameID, listofVariable);

		count += itExec.to< ExecutableForm >().getConstVariable().
					getByQualifiedNameID(aQualifiedNameID, listofVariable);
	}

	return( count );
}


const BF & ExecutableQuery::getVariable(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getAllVariables().getByFQNameID(aFullyQualifiedNameID, true);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getConstVariable().getByFQNameID(aFullyQualifiedNameID, true);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}


const BF & ExecutableQuery::getVariableByAstElement(
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getAllVariables().getByAstElement(astElement);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
		{
			const BF & foundElement = itExec.to< ExecutableForm >().
					getConstVariable().getByAstElement(astElement);

			if( foundElement.valid() )
			{
				return( foundElement );
			}
		}
	}

	return( BF::REF_NULL );
}


// REGEX
std::size_t ExecutableQuery::getVariableByREGEX(
		const std::string & aRedexID, BFList & listofVariable) const
{
	std::size_t count = 0;

	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getAllVariables().
				getByQualifiedNameREGEX(aRedexID, listofVariable);
	}

	return count;
}


std::size_t ExecutableQuery::getVariableByNameREGEX(
		const ExecutableForm & anExecutable,
		const std::string & aRedexID, BFList & listofVariable) const
{
	std::size_t count = anExecutable.getAllVariables().
			getByNameREGEX(aRedexID, listofVariable);

	for( const auto & itModel : anExecutable.getInstanceStatic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getVariableByNameREGEX(
					itModel.getExecutable(), aRedexID, listofVariable );
		}
	}

	for( const auto & itModel : anExecutable.getInstanceDynamic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getVariableByNameREGEX(
					itModel.getExecutable(), aRedexID, listofVariable );
		}
	}

	return count;
}


/**
 * SEARCH
 * Symbol as InstanceOfPort
 * by Name ID
 */
const Symbol & ExecutableQuery::getPortByNameID(
		const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().getPort().getByNameID(aNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getPortByNameID(const std::string & aNameID,
		Modifier::DIRECTION_KIND ioDirection) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().getPort().getByNameID(aNameID);

		if( foundElement.valid()
			&& foundElement.getModifier().isDirectionKind(ioDirection) )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


std::size_t ExecutableQuery::getPortByNameID(
		const std::string & aNameID, ListOfSymbol & listofPort) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getPort().getByNameID(aNameID, listofPort);
	}

	return( count );
}


std::size_t ExecutableQuery::getPortByNameID(
		const std::string & aNameID, ListOfSymbol & listofPort,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getPort().getByNameID(aNameID, listofPort);
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


/**
 * SEARCH
 * Symbol as InstanceOfPort
 * by [ [ FULLY ] QUALIFIED ] NAME ID
 */
const Symbol & ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getPort().getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getPort().getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid()
			&& foundElement.getModifier().
					isDirectionKind(ioDirection, isStrongly) )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


std::size_t ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID, ListOfSymbol & listofPort) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getPort().
				getByQualifiedNameID(aQualifiedNameID, listofPort);
	}

	return( count );
}


std::size_t ExecutableQuery::getPortByQualifiedNameID(
		const std::string & aQualifiedNameID, ListOfSymbol & listofPort,
		Modifier::DIRECTION_KIND ioDirection, bool isStrongly) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getPort().
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


const Symbol & ExecutableQuery::getPort(
		const std::string & aFullyQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getPort().getByFQNameID(aFullyQualifiedNameID, true);

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
	for( ; anExecutable != nullptr ;
			anExecutable = anExecutable->getExecutableContainer() )
	{
		const Symbol & foundElement = anExecutable->getPort().
				getByFQNameID(aFullyQualifiedNameID, true);
		if( foundElement.valid() )
		{
			return foundElement;
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getPortByAstElement(
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().
				getPort().getByAstElement(astElement);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & ExecutableQuery::getSemPortByAstElement(
		const ExecutableForm * anExecutable, const ObjectElement & astElement)
{
	for( ; anExecutable != nullptr ;
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


// REGEX
std::size_t ExecutableQuery::getPortByREGEX(
		const std::string & aRedexID, ListOfSymbol & listofPort) const
{
	std::size_t count = 0;

	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getPort().
				getByQualifiedNameREGEX(aRedexID, listofPort);
	}

	return count;
}


std::size_t ExecutableQuery::getPortByNameREGEX(
		const ExecutableForm & anExecutable,
		const std::string & aRedexID, ListOfSymbol & listofPort) const
{
	std::size_t count = anExecutable.getPort().
			getByNameREGEX(aRedexID, listofPort);

	for( const auto & itModel : anExecutable.getInstanceStatic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getPortByNameREGEX(
					itModel.getExecutable(), aRedexID, listofPort );
		}
	}

	for( const auto & itModel : anExecutable.getInstanceDynamic() )
	{
		if( itModel.ptrExecutable() != (& anExecutable) )
		{
			count += getPortByNameREGEX(
					itModel.getExecutable(), aRedexID, listofPort );
		}
	}

	return count;
}



/**
 * SEARCH
 * InstanceOfChannel
 */
const Symbol & ExecutableQuery::getChannel(
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().
				getChannel().getByAstElement(astElement);

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
				itExec.to< ExecutableForm >().getInstanceByDesign(
				aDesign ).getByFQNameID(aFullyQualifiedNameID, true);

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
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getInstanceByDesign(aDesign).getByNameID(aNamleID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

std::size_t ExecutableQuery::getMachineByNameID(
		Specifier::DESIGN_KIND aDesign, const std::string & aNamleID,
		ListOfSymbol & listofMachine) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getInstanceByDesign(aDesign).
				getByNameID(aNamleID, listofMachine);
	}

	return( count );
}


const Symbol & ExecutableQuery::getMachineByQualifiedNameID(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
			getInstanceByDesign(aDesign).getByQualifiedNameID(aQualifiedNameID);

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

std::size_t ExecutableQuery::getMachineByQualifiedNameID(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aQualifiedNameID,
		ListOfSymbol & listofMachine) const
{
	std::size_t count = 0;

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		count += itExec.to< ExecutableForm >().getInstanceByDesign(aDesign).
				getByQualifiedNameID(aQualifiedNameID, listofMachine);
	}

	return( count );
}



InstanceOfMachine * ExecutableQuery::rawMachineByNameID(
		Specifier::DESIGN_KIND aDesign, const std::string & aNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		InstanceOfMachine * foundElement =
				itExec.to< ExecutableForm >().getInstanceByDesign(
						aDesign ).getByNameID(aNameID).rawMachine();

		if( foundElement != nullptr )
		{
			return( foundElement );
		}
	}

	return( nullptr );
}

InstanceOfMachine * ExecutableQuery::rawMachineByQualifiedNameID(
		Specifier::DESIGN_KIND aDesign,
		const std::string & aQualifiedNameID) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		InstanceOfMachine * foundElement =
				itExec.to< ExecutableForm >().getInstanceByDesign( aDesign ).
				getByQualifiedNameID(aQualifiedNameID).rawMachine();

		if( foundElement != nullptr )
		{
			return( foundElement );
		}
	}

	return( nullptr );
}


const Symbol & ExecutableQuery::getMachineByAstElement(
		Specifier::DESIGN_KIND aDesign, const ObjectElement & astElement) const
{
	if( getSystem().rawSystemInstance()->isAstElement( astElement ) )
	{
		return( getSystem().getSystemInstance() );
	}

	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement = itExec.to< ExecutableForm >().
				getInstanceByDesign(aDesign).getByAstElement(astElement);

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

		InstanceOfMachine * mainMachine = nullptr;

		if( mid.find('.') == std::string::npos )
		{
			mainMachine = rawMachineByNameID(aDesign, mid);
		}
		else
		{
			mainMachine = rawMachineByQualifiedNameID(aDesign, mid);
		}

		if( mainMachine != nullptr )
		{
			if( obj != "[*]" )
			{
				const BF & machine = mainMachine->refExecutable().
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
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
			itExec.to< ExecutableForm >().getByAstInstanceModel( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceModel(
		const ExecutableForm * anExecutable,
		const ObjectElement & astElement) const
{
	for( ; anExecutable != nullptr ;
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
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
			itExec.to< ExecutableForm >().getByAstInstanceStatic( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceStatic(
		const ExecutableForm * anExecutable,
		const ObjectElement & astElement) const
{
	for( ; anExecutable != nullptr ;
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
		const ObjectElement & astElement) const
{
	// REVERSE because machines are insert after children
	for( const auto & itExec : getSystem().getExecutables() )
	{
		const Symbol & foundElement =
			itExec.to< ExecutableForm >().getByAstInstanceDynamic( astElement );

		if( foundElement.valid() )
		{
			return( foundElement );
		}
	}

	return( Symbol::REF_NULL );
}

const Symbol & ExecutableQuery::getSemInstanceDynamic(
		const ExecutableForm * anExecutable,
		const ObjectElement & astElement) const
{
	for( ; anExecutable != nullptr ; anExecutable = anExecutable->getExecutableContainer() )
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
		const ObjectElement & astElement) const
{
	if( getSystem().rawSystemInstance()->isAstElement( astElement ) )
	{
		return( getSystem().getSystemInstance() );
	}

	{
		const BF & foundElement = getVariableByAstElement(astElement);
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
