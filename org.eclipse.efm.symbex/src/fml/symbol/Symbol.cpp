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
#include <fml/executable/InstanceOfConnect.h>
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

InstanceOfBuffer & Symbol::buffer()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfBuffer reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfBuffer & >( *mPTR ) );
}

const InstanceOfBuffer & Symbol::buffer() const
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
	return( buffer().getPolicySpecifierKind() );
}

void Symbol::setPolicySpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
{
	buffer().setPolicySpecifierKind( aSpecifierKind );
}


/**
 * GETTER - SETTER
 * mCapacity
 */
avm_size_t Symbol::capacity() const
{
	return( buffer().capacity() );
}

long Symbol::realCapacity() const
{
	return( buffer().realCapacity() );
}

void Symbol::setCapacity(long aCapacity)
{
	buffer().setCapacity( aCapacity );
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
// InstanceOfConnect
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfConnect & Symbol::connector()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfConnect reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfConnect & >( *mPTR ) );
}

const InstanceOfConnect & Symbol::connector() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfConnect reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfConnect & >( *mPTR ) );
}


InstanceOfConnect * Symbol::rawConnect() const
{
	return( static_cast< InstanceOfConnect * >( mPTR )  );
}


/**
 * GETTER - SETTER
 * mOutputComRouteData
 * mInputComRouteData
 */
const ComRouteData & Symbol::getOutputComRouteData() const
{
	return( connector().getOutputComRouteData() );
}

const ComRouteData & Symbol::getInputComRouteData() const
{
	return( connector().getInputComRouteData() );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// InstanceOfData
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

InstanceOfData & Symbol::data()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfData reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfData & >( *mPTR ) );
}

const InstanceOfData & Symbol::data() const
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfData reference !!!"
			<< SEND_EXIT;

	return( static_cast< const InstanceOfData & >( *mPTR ) );
}


InstanceOfData * Symbol::rawData() const
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
	data().updateFullyQualifiedNameID(aFullyQualifiedNameID, aNameID);
}


/**
 * GETTER - SETTER
 * mPointerNature
 */
IPointerDataNature::POINTER_DATA_NATURE Symbol::getPointerNature() const
{
	return( data().getPointerNature() );
}


/**
 * GETTER - SETTER
 * mValue
 */
BF & Symbol::getValue()
{
	return( data().getValue() );
}

const BF & Symbol::getValue() const
{
	return( data().getValue() );
}

bool Symbol::hasValue() const
{
	return( data().hasValue() );
}

void Symbol::setValue(const BF & aValue)
{
	data().setValue( aValue );
}


// ArrayValue
ArrayBF * Symbol::getArrayValue() const
{
	return( data().getArrayValue() );
}

bool Symbol::hasArrayValue() const
{
	return( data().hasArrayValue() );
}


void Symbol::formatStream(OutStream & os, const BF & aValue) const
{
	data().formatStream(os, aValue);
}

void Symbol::strValue(OutStream & os, const BF & aValue) const
{
	data().strValue(os, aValue);
}

std::string Symbol::strValue(const BF & aValue) const
{
	return( data().strValue(aValue) );
}

std::string Symbol::strValue() const
{
	return( data().strValue() );
}


/**
 * GETTER - SETTER
 * mAttributeTable
 */
TableOfSymbol * Symbol::getAttribute() const
{
	return( data().getAttribute() );
}

const Symbol & Symbol::getAttributeByNameID(const std::string & id) const
{
	return( data().hasAttribute() ?
			data().getAttribute()->getByNameID(id) : Symbol::REF_NULL );
}

bool Symbol::hasAttribute() const
{
	return( data().hasAttribute() );
}

void Symbol::setAttribute(TableOfSymbol * anAttributeTable)
{
	data().setAttribute( anAttributeTable );
}

void Symbol::setAttribute(avm_offset_t offset, const Symbol & aWProperty)
{
	data().setAttribute( offset , aWProperty );
}


/**
 * GETTER - SETTER
 * mRelativeDataPath
 * mRelativeOffsetPath
 */
TableOfSymbol * Symbol::getDataPath() const
{
	return( data().getDataPath() );
}

bool Symbol::hasDataPath() const
{
	return( data().hasDataPath() );
}

void Symbol::setDataPath(TableOfSymbol & aRelativeDataPath)
{
	data().setDataPath( aRelativeDataPath );
}


avm_size_t * Symbol::getOffsetPath() const
{
	return( data().getOffsetPath() );
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
const Machine * Symbol::getAstMachine() const
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
ExecutableForm * Symbol::getExecutable() const
{
	return( machine().getExecutable() );
}

bool Symbol::hasExecutable() const
{
	return( machine().hasExecutable() );
}

void Symbol::setExecutable(ExecutableForm * anExecutable)
{
	machine().setExecutable( anExecutable );
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


void Symbol::setInstanceModel(InstanceOfMachine * anInstanceModel)
{
	machine().setInstanceModel( anInstanceModel );
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

InstanceOfPort & Symbol::port()
{
	AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
			<< "Unexpected a <null> pointer as InstanceOfPort reference !!!"
			<< SEND_EXIT;

	return( static_cast< InstanceOfPort & >( *mPTR ) );
}

const InstanceOfPort & Symbol::port() const
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
avm_size_t Symbol::getRouteOffset() const
{
	return( port().getRouteOffset() );
}

void Symbol::setRouteOffset(avm_size_t aRouteOffset)
{
	port().setRouteOffset( aRouteOffset );
}

/**
 * GETTER - SETTER
 * mInputRoutingData
 * mOutputRoutingData
 */
const RoutingData & Symbol::getInputRoutingData() const
{
	return( port().getInputRoutingData() );
}

inline bool Symbol::hasInputRoutingData() const
{
	return( port().hasInputRoutingData() );
}

void Symbol::setInputRoutingData(const RoutingData & anInputRoutingData)
{
	port().setInputRoutingData( anInputRoutingData );
}


const RoutingData & Symbol::getOutputRoutingData() const
{
	return( port().getOutputRoutingData() );
}

bool Symbol::hasOutputRoutingData() const
{
	return( port().hasOutputRoutingData() );
}

void Symbol::setOutputRoutingData(const RoutingData & anOutputRoutingData)
{
	port().setOutputRoutingData( anOutputRoutingData );
}




} /* namespace sep */
