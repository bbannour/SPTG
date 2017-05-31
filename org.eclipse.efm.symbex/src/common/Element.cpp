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

#include "Element.h"

#include <common/BF.h>

#include <exception>


namespace sep
{


/**
 * GETTER - SETTER
 * for container of BF
 */
BF & Element::at(avm_size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::at( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

const BF & Element::at(avm_size_t offset) const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::at( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


BF & Element::operator[](avm_size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::operator[]( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

const BF & Element::operator[](avm_size_t offset) const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::operator[]( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


BF & Element::getWritable(avm_size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::getWritable( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

void Element::makeWritable(avm_size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::makeWritable( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

void Element::set(avm_size_t offset, const BF & bf)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::set( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

avm_size_t Element::size() const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::size() >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


}
