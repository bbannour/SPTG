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

#include "TableOfTypeSpecifier.h"

#include <fml/executable/InstanceOfData.h>


namespace sep
{


const Symbol & TableOfTypeSpecifier::getSymbolData(
		const std::string & aFullyQualifiedNameID) const
{
	ContainerOfType::const_iterator it = ContainerOfType::begin();
	ContainerOfType::const_iterator endIt = ContainerOfType::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).hasSymbol() )
		{
			const Symbol & foundInstance =
					(*it).getSymbol( aFullyQualifiedNameID );
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}
	}
	return( Symbol::REF_NULL );
}


const Symbol & TableOfTypeSpecifier::getSymbolDataByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	ContainerOfType::const_iterator it = ContainerOfType::begin();
	ContainerOfType::const_iterator endIt = ContainerOfType::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).hasSymbol() )
		{
			const Symbol & foundInstance =
					(*it).getSymbolByQualifiedNameID(aQualifiedNameID);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & TableOfTypeSpecifier::getSymbolDataByNameID(
		const std::string & aNameID) const
{
	ContainerOfType::const_iterator it = ContainerOfType::begin();
	ContainerOfType::const_iterator endIt = ContainerOfType::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).hasSymbol() && (*it).isTypedEnum() )
		{
			const Symbol & foundInstance = (*it).getSymbolByNameID(aNameID);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}
	}

	return( Symbol::REF_NULL );
}


const Symbol & TableOfTypeSpecifier::getSymbolDataByAstElement(
		const ObjectElement * astElement) const
{
	ContainerOfType::const_iterator it = ContainerOfType::begin();
	ContainerOfType::const_iterator endIt = ContainerOfType::end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).hasSymbol() )
		{
			const Symbol & foundInstance =
					(*it).getSymbolByAstElement(astElement);
			if( foundInstance.valid() )
			{
				return( foundInstance );
			}
		}
	}
	return( Symbol::REF_NULL );
}


} /* namespace sep */
