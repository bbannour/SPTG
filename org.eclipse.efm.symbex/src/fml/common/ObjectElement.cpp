/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "ObjectElement.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Package.h>


namespace sep
{



/*
 * ATTRIBUTES
 */
bool ObjectElement::USE_ONLY_ID = false;


/**
 * UTIL
 * return <container-fully-qulified-name-id>.<name-id>
 */
std::string ObjectElement::makeFullyQualifiedNameID(
		const ObjectElement * aContainer, const std::string & aNameID)
{
	if( aContainer == NULL )
	{
		return( FQN_ID_ROOT_SEPARATOR + aNameID );
	}
//	else if( aContainer->is< System >() )
//	{
//		return( "spec::" + id );
//	}
//	else if( aContainer->is< Package >() )
//	{
//		return( "lib::" + aNameID );
//	}
	else
	{
		return( aContainer->getFullyQualifiedNameID() + "." + aNameID );
	}
}

/**
 * GETTER
 * the first Machine container
 */
Machine * ObjectElement::getContainerMachine() const
{
	ObjectElement * container = getContainer();
	for( ; container != NULL ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to< Machine >() );
		}
	}

	return( NULL );
}

/**
 * GETTER
 * the first PropertyElement container
 */
PropertyElement * ObjectElement::getContainerProperty() const
{
	ObjectElement * container = getContainer();
	for( ; container != NULL ; container = container->getContainer() )
	{
		if( container->is< PropertyElement >() )
		{
			return( container->to< PropertyElement >() );
		}
	}

	return( NULL );
}


}
