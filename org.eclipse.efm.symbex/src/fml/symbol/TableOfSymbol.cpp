/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TableOfSymbol.h"

namespace sep
{


const Symbol & TableOfSymbol::getByFQNameID(
		const std::string & aFullyQualifiedNameID) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		// STRICT:> compare LOCATOR & LOCATION [true:- retry only only LOCATION]
		if( (*it).fqnEquals( aFullyQualifiedNameID , true ) )
		{
			return( *it );
		}
	}
	return( Symbol::REF_NULL );
}


const Symbol & TableOfSymbol::getByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).rawSymbol()->fqnEndsWith(aQualifiedNameID) )
		{
			return( *it );
		}
	}
	return( Symbol::REF_NULL );
}


avm_size_t TableOfSymbol::getByQualifiedNameID(
		const std::string & aQualifiedNameID, ListOfSymbol & listofFound) const
{
	avm_size_t count = 0;

	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).rawSymbol()->fqnEndsWith(aQualifiedNameID) )
		{
			listofFound.append( *it );

			++count;
		}
	}

	return( count );
}


const Symbol & TableOfSymbol::getByNameID(const std::string & id) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).getNameID() == id )
		{
			return( *it );
		}
	}
	return( Symbol::REF_NULL );
}


avm_size_t TableOfSymbol::getByNameID(
		const std::string & id, ListOfSymbol & listofFound) const
{
	avm_size_t count = 0;

	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).getNameID() == id )
		{
			listofFound.append( *it );

			++count;
		}
	}

	return( count );
}


const Symbol & TableOfSymbol::getByAstElement(
		const ObjectElement * astElement) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).isAstElement( astElement ) )
		{
			return( *it );
		}
	}
	return( Symbol::REF_NULL );
}


/**
 * contains a particular element
 */
bool TableOfSymbol::contains(ConstPointerBaseT aSymbol) const
{
	if( (aSymbol->getOffset() < size())
		&& (get(aSymbol->getOffset()) == aSymbol) )
	{
		return( true );
	}
	else
	{
		ContainerOfSymbol::const_iterator it = BaseVector::begin();
		ContainerOfSymbol::const_iterator endIt = BaseVector::end();
		for( ; it != endIt ; ++it )
		{
			if( (*it) == aSymbol )
			{
				return( true );
			}
		}

		return( false );
	}
}


bool TableOfSymbol::contains(const BF & aSymbol) const
{
	ContainerOfSymbol::const_iterator it = BaseVector::begin();
	ContainerOfSymbol::const_iterator endIt = BaseVector::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).rawSymbol() == aSymbol.raw_pointer() )
		{
			return( true );
		}
	}

	return( false );
}



/**
 * Serialization
 */
void TableOfSymbol::strHeader(OutStream & os) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		(*it).strHeader( os << TAB ); os << EOL;
	}
}

void TableOfSymbol::toStream(OutStream & os) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		(*it).toStream(os);
	}
}

void TableOfSymbol::toFscn(OutStream & os) const
{
	ContainerOfSymbol::const_iterator it = ContainerOfSymbol::begin();
	ContainerOfSymbol::const_iterator endIt = ContainerOfSymbol::end();
	for( ; it != endIt ; ++it )
	{
		os << TAB << AVM_NO_INDENT;
		(*it).toFscn(os);
		os << END_INDENT_EOL;
	}
}



} /* namespace sep */
