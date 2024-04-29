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

#include <printer/OutStream.h>

#include <util/avm_debug.h>

#include <exception>


namespace sep
{


/**
 * GETTER - SETTER
 * for container of BF
 */
BF & Element::at(std::size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::at( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

const BF & Element::at(std::size_t offset) const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::at( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


BF & Element::operator[](std::size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::operator[]( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

const BF & Element::operator[](std::size_t offset) const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::operator[]( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


BF & Element::getWritable(std::size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::getWritable( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

void Element::makeWritable(std::size_t offset)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::makeWritable( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

void Element::set(std::size_t offset, const BF & bf)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::set( "
			<< str() << " , " << offset << " ) >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}

std::size_t Element::size() const
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Illegal method call << Element::size() >> !!!"
			<< SEND_EXIT;

	throw( std::exception() );
}


/**
 * MEMORY MANAGEMENT
 * DESTROY
 */
void DestroyElementPolicy::destroy(Element * anElement)
{
	if( anElement != nullptr )
	{
		if( anElement->isUnique() )
		{
//			AVM_OS_TRACE << "destroy :> " << anElement->str() << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
	anElement->dbgDestroy();
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )

			delete( anElement );

			anElement = nullptr;
		}

		else if( anElement->getRefCount() == 0 )
		{
//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
//
//			const char * classKindName = anElement->classKindName();
//			std::string strForm = "";//anElement->str();
//
//			AVM_OS_COUT << ">>> destroy Element < " << classKindName
//					<< " > @ " << std::addressof(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_LOG << ">>> destroy Element < " << classKindName
//					<< " > @ " << std::addressof(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//
//			AVM_OS_TRACE << ">>> destroy Element < " << classKindName
//					<< " > @ " << std::addressof(anElement) << " : " << strForm
//					<< " with refCount == 0 !!!"
//					<< std::endl;
//_AVM_ELSE_
//			AVM_OS_WARNING_ALERT << ">>> destroy with refCount == 0 !!!"
//					<< SEND_ALERT;

			AVM_OS_COUT << ">>> destroy Element @ "
					<< std::addressof(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_COUT << "\t>> " << anElement->str() << std::endl;

			AVM_OS_LOG << ">>> destroy Element @ "
					<< std::addressof(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_LOG << "\t>> " << anElement->str() << std::endl;

			AVM_OS_TRACE << "\t>>> destroy Element @ "
					<< std::addressof(anElement)
					<< " with refCount == 0 !!!" << std::endl;
			AVM_OS_TRACE << "\t>> " << anElement->str() << std::endl;

//AVM_IF_DEBUG_LEVEL_FLAG( HIGH , REFERENCE_COUNTING )
		}

		else
		{
			anElement->decrRefCount();
		}
	}
}


}
