/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 24 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "WPropertyImpl.h"

#include <fml/expression/AvmCode.h>
#include <fml/expression/BuiltinArray.h>

#include <fml/operator/Operator.h>

#include <fml/workflow/WObject.h>


namespace sep
{


/**
 * GETTER - SETTER
 * for AvmCode attribue
 */
const BFCode & WPropertyImpl::getAvmCodeValue() const
{
	return( getValue().bfCode() );
}

bool WPropertyImpl::hasAvmCodeValue() const
{
	return( getValue().is< AvmCode >() );
}


/**
 * GETTER
 * for BuiltinArray attribute
 */
BuiltinArray * WPropertyImpl::getBuiltinArrayValue() const
{
	return( getValue().as_ptr< BuiltinArray >() );
}

bool WPropertyImpl::hasBuiltinArrayValue() const
{
	return( getValue().is< BuiltinArray >() );
}


BF WPropertyImpl::getArrayValue() const
{
	if( getValue().is< ArrayBF >() )
	{
		return( getValue() );
	}
	else if( getValue().is< BuiltinArray >() )
	{
		return( BF( getValue().to_ptr< BuiltinArray >()->getArrayBF() ) );
	}

	return( BF::REF_NULL );
}

bool WPropertyImpl::hasArrayValue() const
{
	return( getValue().is< ArrayBF >() );
}


std::string WPropertyImpl::toStringValue(BuiltinArray * anArray, std::size_t offset) const
{
	if( anArray->is< ArrayString >() )
	{
		return( anArray->to_ptr< ArrayString >()->get(offset) );

		//!! No because of default quote char like: "string"
//		return( anArray->to_ptr< ArrayString >()->str(offset) );
	}

	else if( anArray->is< ArrayBF >() )
	{
		return( toStringValue( anArray->to_ptr< ArrayBF >()->at(offset) ) );
	}

	else if( getValue().is< BuiltinArray >() )
	{
		return( anArray->to_ptr< BuiltinArray >()->str(offset) );
	}

	else
	{
		return( toStringValue() );
	}
}


} /* namespace sep */
