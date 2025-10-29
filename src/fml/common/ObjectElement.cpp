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

#include <common/BF.h>

#include <fml/executable/BaseInstanceForm.h>

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
	if( aContainer == nullptr )
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
bool ObjectElement::isContainerMachine() const
{
	return( (mContainer != nullptr) && mContainer->is< Machine >() );
}

Machine * ObjectElement::getContainerMachine() const
{
	ObjectElement * container = getContainer();
	for( ; container != nullptr ; container = container->getContainer() )
	{
		if( container->is< Machine >() )
		{
			return( container->to_ptr< Machine >() );
		}
	}

	return( nullptr );
}

/**
 * GETTER
 * the first PropertyElement container
 */
PropertyElement * ObjectElement::getContainerProperty() const
{
	ObjectElement * container = getContainer();
	for( ; container != nullptr ; container = container->getContainer() )
	{
		if( container->is< PropertyElement >() )
		{
			return( container->to_ptr< PropertyElement >() );
		}
	}

	return( nullptr );
}


/**
 * Serialization
 */
void ObjectElement::toStreamStaticCom(OutStream & out, const BF & comBF)
{
	out << /*TAB <<*/ "{";

	if( comBF.is< ObjectElement >() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )

		out << EOL_TAB2 << str_header( comBF.to_ptr< ObjectElement >() ) << EOL;

AVM_ELSE

		out << EOL_TAB2
			<< comBF.to< BaseInstanceForm >().getFullyQualifiedNameID()
			<< EOL;

AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , COMMUNICATION )
	}
	else if( comBF.is< AvmCode >() )
	{
		if( comBF.to< AvmCode >().hasOperand() )
		{
			ScopeIncrIndent asii(out);

			comBF.to< AvmCode >().toStreamRoutine( out );
		}
		else
		{
			//!! EMPTY
		}
	}
	else
	{
		comBF.toStream( out << EOL_INCR_INDENT );
		out << DECR_EOL;
	}

	out << TAB << "}" << EOL;
}


}
