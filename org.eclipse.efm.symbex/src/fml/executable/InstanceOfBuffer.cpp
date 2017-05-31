/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "InstanceOfBuffer.h"

#include <fml/common/ObjectElement.h>

#include <fml/executable/ExecutableForm.h>

#include <fml/infrastructure/Buffer.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/infrastructure/Buffer.h>


namespace sep
{


static const TypeSpecifier & getSpecifierType(
		BaseAvmProgram * aContainer, Buffer * aBuffer)
{
//	TypeSpecifier bfTS( TypeManager::newCollection(
//			aBuffer, aBuffer->getPolicySpecifierKind(),
//			TypeManager::UNIVERSAL, aBuffer->getCapacity()) );
//
//	return( bfTS );

	return( TypeManager::BUFFER );
}

static const TypeSpecifier & getSpecifierType(BaseAvmProgram * aContainer,
		avm_type_specifier_kind_t aSpecifierKind, avm_size_t aCapacity)
{
//	TypeSpecifier bfTS( TypeManager::newCollection(DataType::BUFFER,
//			aSpecifierKind, TypeManager::UNIVERSAL, aCapacity) );
//
//	return( bfTS );

	return( TypeManager::BUFFER );
}


/**
 * CONSTRUCTOR
 * Default
 */
InstanceOfBuffer::InstanceOfBuffer(
		BaseAvmProgram * aContainer, Buffer * aBuffer, avm_offset_t anOffset)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfBuffer ), aContainer, aBuffer,
		getSpecifierType(aContainer, aBuffer), anOffset),
mPolicySpecifierKind( aBuffer->getPolicySpecifierKind() ),
mCapacity( aBuffer->getCapacity() )
{

}


InstanceOfBuffer::InstanceOfBuffer(	BaseAvmProgram * aContainer,
		Buffer * aCompiled, avm_offset_t anOffset,
		avm_type_specifier_kind_t aSpecifierKind, long aCapacity)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfBuffer ), aContainer, aCompiled,
		getSpecifierType(aContainer, aSpecifierKind, aCapacity), anOffset),
mPolicySpecifierKind( aSpecifierKind ),
mCapacity( (aCapacity < 0) ? AVM_NUMERIC_MAX_SIZE_T : aCapacity )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void InstanceOfBuffer::strHeader(OutStream & out) const
{
	out << "buffer< id:" << getOffset() << " > "
		<< Buffer::str(mPolicySpecifierKind, realCapacity()) << " "
		<< getFullyQualifiedNameID();
}


void InstanceOfBuffer::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	bool isEmpty = true;

	out << TAB << getModifier().toString()
		<< "buffer< id:" << getOffset() << " > "
		<< Buffer::str(mPolicySpecifierKind, realCapacity())
		<< " " << getFullyQualifiedNameID();
	AVM_DEBUG_REF_COUNTER(out);


AVM_IF_DEBUG_FLAG( COMPILING )
	out << " {" << EOL; isEmpty = false;

	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}

	out << TAB2 << "//container = "
		<< (hasContainer() ? getContainer()->getFullyQualifiedNameID() : "NULL")
		<< ";" << EOL;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	if( hasAliasTarget() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as< InstanceOfBuffer >() )
			<< ";" << EOL;
	}

	if( hasCreatorContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#creator = " << getCreatorContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeContainerRID() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }
		out << TAB2 << "rid#container = " << getRuntimeContainerRID().str()
			<< ";" << EOL;
	}

	if( hasMachinePath() )
	{
		if( isEmpty ) { out << " {" << EOL; isEmpty = false; }

		out << TAB << "path#machine:" << EOL;
		ArrayOfInstanceOfMachine::const_iterator it = getMachinePath()->begin();
		ArrayOfInstanceOfMachine::const_iterator endIt = getMachinePath()->end();
		for( ; it != endIt ; ++it )
		{
			out << TAB2 << (*it)->getFullyQualifiedNameID() << EOL;
		}
	}

	( isEmpty ? (out << ";") : (out << TAB << "}") ) << EOL_FLUSH;
}



}
