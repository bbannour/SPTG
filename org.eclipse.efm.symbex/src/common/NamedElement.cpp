/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "NamedElement.h"

#include <util/avm_string.h>

#include <boost/tokenizer.hpp>


namespace sep
{

/**
* GLOBALS
* NAME ID SEPARATOR
*/
std::string NamedElement::NAME_ID_SEPARATOR = "#";

const std::regex NamedElement::REGEX_DOT_or_DIESE          = std::regex("[.#]+");

const std::regex NamedElement::REGEX_DOT_or_COLON_or_DIESE = std::regex("[.:#]+");

/**
 * ATTRIBUTES
 */
const std::string NamedElement::UNNAMED_ID = "<name-id:?>";


/**
 * UTILS
 */
std::string NamedElement::relativeQualifiedNameID(
		const NamedElement & anElement) const
{
	std::string thisLocationID = getLocationID();
	std::string anElementLocationID = anElement.getLocationID();

	if( StringTools::stricklyStartsWith(thisLocationID, anElementLocationID) )
	{
		return( thisLocationID.substr(anElementLocationID.size() + 1) );
	}

	return( getFullyQualifiedNameID() );
}

/*
 * UTIL
 * return suffix of <container-id>.<name-id> i.e. <name-id>
 */
std::string NamedElement::extractNameID(const std::string & aQualifiedNameID)
{
	if( not aQualifiedNameID.empty() )
	{
		std::string::size_type pos = aQualifiedNameID.find_last_of('.');

		if( pos != std::string::npos )
		{
			return( aQualifiedNameID.substr(pos + 1) );
		}
		else
		{
			pos = aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

			if( pos != std::string::npos )
			{
				return( aQualifiedNameID.substr(pos + 2) );
			}
		}
	}

	return( aQualifiedNameID );
}


/**
 * UTIL
 * return <container-id>.<name-id>
 * return <fqn> without <system-id>
 */
std::string NamedElement::makeQualifiedNameID(
		const std::string & aQualifiedNameID)
{
	std::string::size_type posLocator =
			aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

	if( posLocator != std::string::npos )
	{
		std::string::size_type posLocation = aQualifiedNameID.find('.');

		if( (posLocation != std::string::npos) && (posLocation > posLocator) )
		{
AVM_IF_DEBUG_FLAG( ALL_NAME_ID )

			return( OSS() << aQualifiedNameID.substr(0, posLocator) << ":"
					<< aQualifiedNameID.substr(posLocation + 1) );
AVM_ELSE

			return( aQualifiedNameID.substr(posLocation + 1) );

AVM_ENDIF_DEBUG_FLAG( ALL_NAME_ID )
		}
	}

	return( aQualifiedNameID );
}

std::string NamedElement::makeQualifiedNameID(
		const std::string & aQualifiedNameID, const std::string & aNameID)
{
	std::string::size_type posLocator =
			aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

	if( posLocator != std::string::npos )
	{
		std::string::size_type posLocation = aQualifiedNameID.find_last_of('.',
				(aQualifiedNameID.size() - aNameID.size() - 2) );

		if( (posLocation != std::string::npos) && (posLocation > posLocator) )
		{
AVM_IF_DEBUG_FLAG( ALL_NAME_ID )

			return( OSS() << aQualifiedNameID.substr(0, posLocator) << ":"
					<< aQualifiedNameID.substr(posLocation + 1) );
AVM_ELSE

			return( aQualifiedNameID.substr(posLocation + 1) );

AVM_ENDIF_DEBUG_FLAG( ALL_NAME_ID )
		}
	}

	return( aQualifiedNameID );
}


std::string NamedElement::makeFullyQualifiedNameID(
		const std::string & aFullyQualifiedNameID,
		const std::string & aQualifiedNameID, bool preserveLocator)
{
	std::string newFQNID = aFullyQualifiedNameID + '.' + aQualifiedNameID;

	std::string::size_type posLocation = newFQNID.find(FQN_ID_ROOT_SEPARATOR);

	if( posLocation != std::string::npos )
	{
		return( preserveLocator ? newFQNID : newFQNID.substr(posLocation) );
	}
	else
	{
		return( FQN_ID_ROOT_SEPARATOR + newFQNID );
	}
}


std::string NamedElement::makeFullyRegexQualifiedNameID(
		const std::string & aFullyQualifiedNameID,
		const std::string & aQualifiedNameID, bool preserveLocator)
{
	std::string newFQNID = aFullyQualifiedNameID + ".*\\." + aQualifiedNameID;

	std::string::size_type posLocation = newFQNID.find(FQN_ID_ROOT_SEPARATOR);

	if( posLocation != std::string::npos )
	{
		return( preserveLocator
				? newFQNID
				: ( ".*" + newFQNID.substr(posLocation) ) );
	}
	else
	{
		return( FQN_ID_ROOT_SEPARATOR + newFQNID );
	}
}


std::string NamedElement::getContainerQualifiedNameID(
		const std::string & aQualifiedNameID)
{
	if( not aQualifiedNameID.empty() )
	{
		std::string::size_type pos = aQualifiedNameID.find_last_of('.');

		if( pos != std::string::npos )
		{
			return( aQualifiedNameID.substr(0, pos) );
		}
		else
		{
			pos = aQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);

			if( pos != std::string::npos )
			{
				return( aQualifiedNameID.substr(pos + 2) );
			}
			else
			{
				return( "" );
			}
		}
	}

	return( aQualifiedNameID );
}


/*
 *******************************************************************************
 * COMPARER  FOR  QUALIFIED NAME ID  STRING
 *******************************************************************************
 */
bool NamedElement::isEqualsID(
		const std::string & aQualifiedNameID, op_comparer_t op) const
{
	switch( op )
	{
		case OP_STRONG_COMPARER   :
			return( (mFullyQualifiedNameID == aQualifiedNameID)
					|| this->isLocationID(aQualifiedNameID) );

		case OP_STRICT_COMPARER   :
			return( mFullyQualifiedNameID == aQualifiedNameID );

		case OP_ABSOLUTE_COMPARER :
			return( this->isLocationID(aQualifiedNameID) );

		case OP_RELATIVE_COMPARER :
			return( this->fqnEndsWith(aQualifiedNameID) );

		case OP_NAME_ID_COMPARER  :
			return( mNameID == aQualifiedNameID );

		case OP_UNRESTRICTED_NAME_COMPARER :
			return( mUnrestrictedName == aQualifiedNameID );

		default:
		{
			if( (op & OP_STRICT_COMPARER)
				&& (mFullyQualifiedNameID == aQualifiedNameID) )
			{
				return( true );
			}
			if( (op & OP_ABSOLUTE_COMPARER)
				&& this->isLocationID(aQualifiedNameID) )
			{
				return( true );
			}
			if( (op & OP_RELATIVE_COMPARER )
				&& this->fqnEndsWith(aQualifiedNameID) )
			{
				return( true );
			}
			if( (op & OP_NAME_ID_COMPARER)
				&& (mNameID == aQualifiedNameID) )
			{
				return( true );
			}

			if( (op & OP_UNRESTRICTED_NAME_COMPARER)
				&& (mNameID == aQualifiedNameID) )
			{
				return( true );
			}

			return( false );
		}
	}
}


/**
 * REGEX MATCH
 */
bool NamedElement::fqnRegexMatch(const std::string & aRegex) const
{
	return( REGEX_MATCH(mFullyQualifiedNameID, aRegex) );
}

bool NamedElement::nameRegexMatch(const std::string & aRegex) const
{
	return( REGEX_MATCH(mNameID, aRegex) );
}


/*
 *******************************************************************************
 * LIST of ID of QUALIFIED NAME ID
 *******************************************************************************
 */
std::size_t NamedElement::collectNameID(Collection< std::string > & listNameID,
		const std::string & aQualifiedNameID, std::string::size_type pos)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( pos < aQualifiedNameID.size() )
			<< "Bad string position in NamedElement::listofID("
			<< aQualifiedNameID << " , " << pos << " )"
			<< SEND_EXIT;

	const std::string & subQualifiedNameID = aQualifiedNameID.substr(pos);

	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
	boost::char_separator<char> sep(".");

	tokenizer tokens(subQualifiedNameID, sep);
	std::size_t count = 0;
	tokenizer::iterator it = tokens.begin();
	for( ; it != tokens.end() ; ++it , ++count )
	{
		listNameID.append((std::string) (*it));
	}

	return( count );
}


std::size_t NamedElement::collectNameID(Collection< std::string > & listNameID,
		const std::string & aQualifiedNameID)
{
	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
	boost::char_separator<char> sep(".");

	tokenizer tokens(aQualifiedNameID, sep);
	std::size_t count = 0;
	tokenizer::iterator it = tokens.begin();
	for( ; it != tokens.end() ; ++it , ++count )
	{
		listNameID.append((std::string) (*it));
	}

	return( count );
}



} /* namespace sep */
