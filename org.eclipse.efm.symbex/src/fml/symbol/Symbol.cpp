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

#include "Symbol.h"

#include <common/BF.h>

#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnector.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>

#include <fml/symbol/TableOfSymbol.h>


namespace sep
{


/**
 * DEFAULT NULL
 */
Symbol Symbol::REF_NULL;


/**
 * ASSIGNMENT
 * BF
 */
inline Symbol & Symbol::operator=(const BF & aSymbol)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aSymbol.is_weakly< BaseInstanceForm >() )
			<< "Invalid Assignment Cast in a Symbol of " << aSymbol.str()
			<< SEND_EXIT;

	if( mPTR != aSymbol.raw_pointer() )
	{
		AVM_ASSIGN_STMNT_DEBUG_SYMBOL_PTR( aSymbol.raw_pointer() )

		release_acquire( aSymbol.to_ptr< BaseInstanceForm >() );
	}
	return( *this );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfBuffer
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfBuffer & Symbol::asBuffer()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfBuffer reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfBuffer & >( *mPTR ) );
}

const InstanceOfBuffer & Symbol::asBuffer() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfBuffer reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfBuffer & >( *mPTR ) );
}


InstanceOfBuffer * Symbol::rawBuffer() const
{
	return( static_cast< InstanceOfBuffer * >( mPTR )  );
}


/**
 * GETTER - SETTER
 * mPolicySpecifierKind
 */
avm_type_specifier_kind_t Symbol::getPolicySpecifierKind() const
{
	return( asBuffer().getPolicySpecifierKind() );
}

void Symbol::setPolicySpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
{
	asBuffer().setPolicySpecifierKind( aSpecifierKind );
}


/**
 * GETTER - SETTER
 * mCapacity
 */
std::size_t Symbol::getCapacity() const
{
	return( asBuffer().getCapacity() );
}

long Symbol::realCapacity() const
{
	return( asBuffer().realCapacity() );
}

void Symbol::setCapacity(long aCapacity)
{
	asBuffer().setCapacity( aCapacity );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfChannel
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfPort & Symbol::channel()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfPort reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfPort & >( *mPTR ) );
}

const InstanceOfPort & Symbol::channel() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfPort reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfPort & >( *mPTR ) );
}


InstanceOfPort * Symbol::rawChannel() const
{
	return( static_cast< InstanceOfPort * >( mPTR )  );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfConnector
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfConnector & Symbol::asConnector()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfConnector reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfConnector & >( *mPTR ) );
}

const InstanceOfConnector & Symbol::asConnector() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfConnector reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfConnector & >( *mPTR ) );
}


InstanceOfConnector * Symbol::rawConnector() const
{
	return( static_cast< InstanceOfConnector * >( mPTR )  );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfData
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfData & Symbol::variable()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfData reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfData & >( *mPTR ) );
}

const InstanceOfData & Symbol::variable() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfData reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfData & >( *mPTR ) );
}


InstanceOfData * Symbol::rawVariable() const
{
	return( static_cast< InstanceOfData * >( mPTR )  );
}


/**
 * SETTER
 * mFullyQualifiedNameID
 */
void Symbol::updateFullyQualifiedNameID(
		const std::string & aFullyQualifiedNameID, const std::string & aNameID)
{
	variable().updateFullyQualifiedNameID(aFullyQualifiedNameID, aNameID);
}


/**
 * GETTER - SETTER
 * mPointerNature
 */
IPointerVariableNature::POINTER_VARIABLE_NATURE Symbol::getPointerNature() const
{
	return( variable().getPointerNature() );
}


/**
 * GETTER - SETTER
 * mValue
 */
BF & Symbol::getValue()
{
	return( variable().getValue() );
}

const BF & Symbol::getValue() const
{
	return( variable().getValue() );
}

bool Symbol::hasValue() const
{
	return( variable().hasValue() );
}

void Symbol::setValue(const BF & aValue)
{
	variable().setValue( aValue );
}


// ArrayValue
ArrayBF * Symbol::getArrayValue() const
{
	return( variable().getArrayValue() );
}

bool Symbol::hasArrayValue() const
{
	return( variable().hasArrayValue() );
}


void Symbol::formatStream(OutStream & os, const BF & aValue) const
{
	variable().formatStream(os, aValue);
}

void Symbol::strValue(OutStream & os, const BF & aValue) const
{
	variable().strValue(os, aValue);
}

std::string Symbol::strValue(const BF & aValue) const
{
	return( variable().strValue(aValue) );
}

std::string Symbol::strValue() const
{
	return( variable().strValue() );
}


/**
 * GETTER - SETTER
 * mAttributeTable
 */
TableOfSymbol * Symbol::getAttribute() const
{
	return( variable().getAttribute() );
}

const Symbol & Symbol::getAttributeByNameID(const std::string & id) const
{
	return( variable().hasAttribute() ?
			variable().getAttribute()->getByNameID(id) : Symbol::REF_NULL );
}

bool Symbol::hasAttribute() const
{
	return( variable().hasAttribute() );
}

void Symbol::setAttribute(TableOfSymbol * anAttributeTable)
{
	variable().setAttribute( anAttributeTable );
}

void Symbol::setAttribute(avm_offset_t offset, const Symbol & aWProperty)
{
	variable().setAttribute( offset , aWProperty );
}


/**
 * GETTER - SETTER
 * mRelativeDataPath
 * mRelativeOffsetPath
 */
TableOfSymbol * Symbol::getDataPath() const
{
	return( variable().getDataPath() );
}

bool Symbol::hasDataPath() const
{
	return( variable().hasDataPath() );
}

void Symbol::setDataPath(TableOfSymbol & aRelativeDataPath)
{
	variable().setDataPath( aRelativeDataPath );
}


std::size_t * Symbol::getOffsetPath() const
{
	return( variable().getOffsetPath() );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfMachine
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfMachine & Symbol::machine()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfMachine reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfMachine & >( *mPTR ) );
}

const InstanceOfMachine & Symbol::machine() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfMachine reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfMachine & >( *mPTR ) );
}


InstanceOfMachine * Symbol::rawMachine() const
{
	return( static_cast< InstanceOfMachine * >( mPTR ) );
}

/**
 * GETTER
 * Specifier
 */
const Specifier & Symbol::getSpecifier() const
{
	return( machine().getSpecifier() );
}

/**
 * GETTER
 * Compiled ObjectElement as Compiled Machine
 */
const Machine & Symbol::getAstMachine() const
{
	return( machine().getAstMachine() );
}


/**
 * GETTER
 * THIS
 */
bool Symbol::isThis() const
{
	return( machine().isThis() );
}

bool Symbol::isnotThis(const ExecutableForm * anExecutable) const
{
	return( machine().isnotThis( anExecutable ) );
}

/**
 * GETTER - SETTER
 * mExecutable
 */
const ExecutableForm & Symbol::getExecutable() const
{
	return( machine().refExecutable() );
}

ExecutableForm & Symbol::getExecutable()
{
	return( machine().refExecutable() );
}

const ExecutableForm * Symbol::ptrExecutable() const
{
	return( machine().getExecutable() );
}

bool Symbol::hasExecutable() const
{
	return( machine().hasExecutable() );
}


/**
 * GETTER - SETTER
 * mInstanceModel
 */
InstanceOfMachine * Symbol::getInstanceModel() const
{
	return( machine().getInstanceModel() );
}

bool Symbol::hasInstanceModel() const
{
	return( machine().hasInstanceModel() );
}

bool Symbol::isInstanceModel(InstanceOfMachine * anInstanceModel) const
{
	return( machine().isInstanceModel(anInstanceModel) );
}


/**
 * GETTER - SETTER
 * mParam
 * mParamReturnTable
 * mReturnOffset
 */
bool Symbol::hasParam() const
{
	return( machine().hasParam() );
}

/**
 * GETTER - SETTER
 * mRuntimeRID
 */
const RuntimeID & Symbol::getRuntimeRID() const
{
	return( machine().getRuntimeRID() );
}

bool Symbol::hasRuntimeRID() const
{
	return( machine().hasRuntimeRID() );
}

void Symbol::setRuntimeRID(const RuntimeID & aRID)
{
	machine().setRuntimeRID( aRID );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfPort
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfPort & Symbol::asPort()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfPort reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfPort & >( *mPTR ) );
}

const InstanceOfPort & Symbol::asPort() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfPort reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfPort & >( *mPTR ) );
}


InstanceOfPort * Symbol::rawPort() const
{
	return( static_cast< InstanceOfPort * >( mPTR )  );
}


/**
 * GETTER - SETTER
 * mRouteOffset
 */
std::size_t Symbol::getRouteOffset() const
{
	return( asPort().getRouteOffset() );
}

void Symbol::setRouteOffset(std::size_t aRouteOffset)
{
	asPort().setRouteOffset( aRouteOffset );
}

/**
 * GETTER - SETTER
 * mInputRoutingData
 * mOutputRoutingData
 */
const RoutingData & Symbol::getInputRoutingData() const
{
	return( asPort().getInputRoutingData() );
}

inline bool Symbol::hasInputRoutingData() const
{
	return( asPort().hasInputRoutingData() );
}

void Symbol::setInputRoutingData(const RoutingData & anInputRoutingData)
{
	asPort().setInputRoutingData( anInputRoutingData );
}


const RoutingData & Symbol::getOutputRoutingData() const
{
	return( asPort().getOutputRoutingData() );
}

bool Symbol::hasOutputRoutingData() const
{
	return( asPort().hasOutputRoutingData() );
}

void Symbol::setOutputRoutingData(const RoutingData & anOutputRoutingData)
{
	asPort().setOutputRoutingData( anOutputRoutingData );
}




} /* namespace sep */
