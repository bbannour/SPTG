/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TypeSpecifier.h"

#include <common/BF.h>

#include <fml/symbol/Symbol.h>

#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/TypeAliasSpecifier.h>
#include <fml/type/ClassTypeSpecifier.h>
#include <fml/type/EnumTypeSpecifier.h>
#include <fml/type/ContainerTypeSpecifier.h>
#include <fml/type/IntervalTypeSpecifier.h>
#include <fml/type/UnionTypeSpecifier.h>


namespace sep
{

/**
 * ASSIGNMENT
 * BF
 */
TypeSpecifier & TypeSpecifier::operator=(const BF & aType)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aType.is_weakly< BaseTypeSpecifier >() )
			<< "Invalid Assignment Cast in a Type of " << aType.str()
			<< SEND_EXIT;

	if( mPTR != aType.raw_pointer() )
	{
		AVM_ASSIGN_STMNT_DEBUG_TYPE_PTR( aType.raw_pointer() )

		release( static_cast< BaseTypeSpecifier * >( aType.raw_pointer() ) );
	}
	return( *this );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// TypeAliasSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

TypeAliasSpecifier & TypeSpecifier::alias()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as TypeAliasSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< TypeAliasSpecifier & >( *mPTR ) );
}

const TypeAliasSpecifier & TypeSpecifier::alias() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as TypeAliasSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const TypeAliasSpecifier & >( *mPTR ) );
}


TypeAliasSpecifier * TypeSpecifier::rawAlias() const
{
	return( static_cast< TypeAliasSpecifier * >( mPTR )  );
}


const BaseTypeSpecifier & TypeSpecifier::aliasTypeSpecifier() const
{
	return( rawAlias()->targetTypeSpecifier() );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// BaseSymbolTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

BaseSymbolTypeSpecifier * TypeSpecifier::rawSymbol() const
{
	return( static_cast< BaseSymbolTypeSpecifier * >( mPTR )  );
}


/**
 * GETTER - SETTER
 * theSymbolData
 */
void TypeSpecifier::saveSymbol(InstanceOfData * anInstance)
{
	rawSymbol()->saveSymbolData( anInstance );
}


const Symbol & TypeSpecifier::getSymbol(
		const std::string & aFullyQualifiedNameID) const
{
	return( rawSymbol()->getSymbolData( aFullyQualifiedNameID ) );
}

const Symbol & TypeSpecifier::getSymbolByQualifiedNameID(
		const std::string & aQualifiedNameID) const
{
	return( rawSymbol()->getDataByQualifiedNameID( aQualifiedNameID ) );
}

const Symbol & TypeSpecifier::getSymbolByNameID(
		const std::string & aNameID) const
{
	return( rawSymbol()->getDataByNameID( aNameID ) );
}


const Symbol & TypeSpecifier::getSymbolByAstElement(
		const ObjectElement & astElement) const
{
	return( rawSymbol()->getDataByAstElement( astElement ) );
}


bool TypeSpecifier::hasSymbol() const
{
	return( is< BaseSymbolTypeSpecifier >() &&
			rawSymbol()->hasSymbolData() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ClassTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ClassTypeSpecifier & TypeSpecifier::classT()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as ClassTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< ClassTypeSpecifier & >( *mPTR ) );
}

const ClassTypeSpecifier & TypeSpecifier::classT() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as ClassTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const ClassTypeSpecifier & >( *mPTR ) );
}


ClassTypeSpecifier * TypeSpecifier::rawClass() const
{
	return( static_cast< ClassTypeSpecifier * >( mPTR )  );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// EnumTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

EnumTypeSpecifier & TypeSpecifier::enumT()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as EnumTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< EnumTypeSpecifier & >( *mPTR ) );
}

const EnumTypeSpecifier & TypeSpecifier::enumT() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as EnumTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const EnumTypeSpecifier & >( *mPTR ) );
}


EnumTypeSpecifier * TypeSpecifier::rawEnum() const
{
	return( static_cast< EnumTypeSpecifier * >( mPTR )  );
}


bool TypeSpecifier::hasSymbolDataWithValue(const BF & aValue) const
{
	return( rawEnum()->hasSymbolDataWithValue(aValue) );
}

const Symbol & TypeSpecifier::getSymbolDataByValue(const BF & aValue) const
{
	return( rawEnum()->getSymbolDataByValue(aValue) );
}


std::size_t TypeSpecifier::getRandomSymbolOffset()
{
	return( rawEnum()->getRandomSymbolOffset() );
}

const Symbol & TypeSpecifier::getRandomSymbolData()
{
	return( rawEnum()->getRandomSymbolData() );
}

const BF & TypeSpecifier::getRandomSymbolValue()
{
	return( rawEnum()->getRandomSymbolValue() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// ContainerTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

ContainerTypeSpecifier & TypeSpecifier::container()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as ContainerTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< ContainerTypeSpecifier & >( *mPTR ) );
}

const ContainerTypeSpecifier & TypeSpecifier::container() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as ContainerTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const ContainerTypeSpecifier & >( *mPTR ) );
}


ContainerTypeSpecifier * TypeSpecifier::rawContainer() const
{
	return( static_cast< ContainerTypeSpecifier * >( mPTR )  );
}


/**
 * theContentsTypeSpecifier
 */
const TypeSpecifier & TypeSpecifier::getContentsTypeSpecifier() const
{
	return( rawContainer()->getContentsTypeSpecifier() );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// IntervalTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

IntervalTypeSpecifier & TypeSpecifier::interval()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as IntervalTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< IntervalTypeSpecifier & >( *mPTR ) );
}

const IntervalTypeSpecifier & TypeSpecifier::interval() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as IntervalTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const IntervalTypeSpecifier & >( *mPTR ) );
}


IntervalTypeSpecifier * TypeSpecifier::rawInterval() const
{
	return( static_cast< IntervalTypeSpecifier * >( mPTR )  );
}

/**
 * theIntervalTypeSpecifier
 */
const TypeSpecifier & TypeSpecifier::getSupportTypeSpecifier() const
{
	return( rawInterval()->getSupportTypeSpecifier() );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// UnionTypeSpecifier
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

UnionTypeSpecifier & TypeSpecifier::unionT()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as UnionTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< UnionTypeSpecifier & >( *mPTR ) );
}

const UnionTypeSpecifier & TypeSpecifier::unionT() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<<  "Unexpected a <null> pointer as UnionTypeSpecifier reference !!!"
			<< SEND_EXIT;

	return( static_cast< const UnionTypeSpecifier & >( *mPTR ) );
}


UnionTypeSpecifier * TypeSpecifier::rawUnion() const
{
	return( static_cast< UnionTypeSpecifier * >( mPTR )  );
}



} /* namespace sep */
