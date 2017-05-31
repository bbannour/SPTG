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

#include "InstanceOfConnect.h"

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/infrastructure/Connector.h>

#include <fml/runtime/RuntimeID.h>

#include <fml/type/TypeManager.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
InstanceOfConnect::InstanceOfConnect(BaseAvmProgram * aContainer,
		const Connector * aConnector, avm_offset_t anOffset,
		ComProtocol::PROTOCOL_KIND aProtocol, ComProtocol::PROTOCOL_KIND aCast)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfConnect ), aContainer, aConnector,
		TypeManager::CONNECTOR, anOffset),
mTransfertFlag( false ),

mMID( 0 ),

mProtocol( aProtocol ),
mCast( aCast ),

mOutputComRouteData( aConnector , Modifier::DIRECTION_OUTPUT_KIND ),
mInputComRouteData ( aConnector , Modifier::DIRECTION_INPUT_KIND  )
{
	//!! NOTHING
}



/**
 * Serialization
 */
void InstanceOfConnect::strHeader(OutStream & out) const
{
	out << "connector< id:" << getOffset() << " , mid:" << getMID() << " > "
		<< Connector::strProtocol(mProtocol, mCast)
		<< " " << getFullyQualifiedNameID();
}


void InstanceOfConnect::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << getModifier().toString() << "connector< id:" << getOffset()
		<< " , mid:" << getMID() << " , "
		<< Connector::strProtocol(mProtocol, mCast) << " > "
		<< getFullyQualifiedNameID();
	AVM_DEBUG_REF_COUNTER(out);
	out << " {" << EOL;

AVM_IF_DEBUG_FLAG( COMPILING )
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
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as< InstanceOfConnect >() )
			<< ";" << EOL;
	}

	if( hasCreatorContainerRID() )
	{
		out << TAB2 << "rid#creator = " << getCreatorContainerRID().str()
			<< ";" << EOL;
	}

	if( hasRuntimeContainerRID() )
	{
		out << TAB2 << "rid#container = " << getRuntimeContainerRID().str()
			<< ";" << EOL;
	}

	if( hasMachinePath() )
	{
		out << TAB << "path#machine:" << EOL;
		ArrayOfInstanceOfMachine::const_iterator it = getMachinePath()->begin();
		ArrayOfInstanceOfMachine::const_iterator endIt = getMachinePath()->end();
		for( ; it != endIt ; ++it )
		{
			out << TAB2 << (*it)->getFullyQualifiedNameID() << EOL;
		}
	}

	out << INCR_INDENT;

	if( hasOutputComRouteData() )
	{
		getOutputComRouteData().toStream(out);
	}

	if( hasInputComRouteData() )
	{
		getInputComRouteData().toStream(out);
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}



}
