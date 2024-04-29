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

#include "InstanceOfConnector.h"

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
InstanceOfConnector::InstanceOfConnector(BaseAvmProgram * aContainer,
		const Connector & astConnector, avm_offset_t anOffset,
		ComProtocol::PROTOCOL_KIND aProtocol,
		ComProtocol::PROTOCOL_KIND aGlobalCast)
: BaseInstanceForm(CLASS_KIND_T( InstanceOfConnector ),
		aContainer, astConnector, TypeManager::CONNECTOR, anOffset),
mTransfertFlag( false ),

mMID( 0 ),

mProtocol( aProtocol ),

mGlobalCast( aGlobalCast ),

mOutputProtocolCast( ComProtocol::PROTOCOL_UNDEFINED_KIND ),
mInputProtocolCast ( ComProtocol::PROTOCOL_UNDEFINED_KIND ),

mOutputRoutingDataTable( ),
mInputRoutingDataTable( )
{
	//!! NOTHING
}



/**
 * Serialization
 */
void InstanceOfConnector::strHeader(OutStream & out) const
{
	out << "connector< id:" << getOffset() << " , mid:" << getMID() << " > "
		<< Connector::strProtocol(mProtocol, mGlobalCast)
		<< " " << getFullyQualifiedNameID();
}


static void strPM(OutStream & out, const PairMachinePort & mp)
{
	out << mp.first().getFullyQualifiedNameID() << "->" << mp.second().getNameID();
}

void InstanceOfConnector::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << getModifier().toString() << "connector< id:" << getOffset()
		<< " , mid:" << getMID() << " , "
		<< Connector::strProtocol(mProtocol, mGlobalCast) << " > "
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
		<< (hasContainer() ? getContainer()->getFullyQualifiedNameID() : "nullptr")
		<< ";" << EOL;
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	if( hasAliasTarget() )
	{
		out << TAB2 << "target = "
			<< str_header( getAliasTarget()->as_ptr< InstanceOfConnector >() )
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

	if( hasOutputRoutingData() )
	{
		out << TAB << "output";
		if( hasOutputProtocolCast() )
		{
			out << "< " << ComProtocol::to_string( getOutputProtocolCast() )
				<< " >";
		}

		if( getOutputRoutingDataTable().singleton() )
		{
			out << " ";
			strPM(out, getOutputRoutingDataTable().first().getMachinePort());
			out << ";" << EOL_FLUSH;
		}
		else if( getOutputRoutingDataTable().nonempty() )
		{
			out << " {" << EOL;
			for( const auto & itRoutingData : getOutputRoutingDataTable() )
			{
				out << TAB2;
				strPM(out, itRoutingData.getMachinePort());
				out << ";" << EOL;
			}
			out << TAB << "}" << EOL_FLUSH;
		}
	}

	if( hasInputRoutingData() )
	{
		out << TAB << "input";
		if( hasInputProtocolCast() )
		{
			out << "< " << ComProtocol::to_string( getInputProtocolCast() )
				<< " >";
		}

		if( getInputRoutingDataTable().singleton() )
		{
			out << " ";
			strPM(out, getInputRoutingDataTable().first().getMachinePort());
			out << ";" << EOL_FLUSH;
		}
		else if( getInputRoutingDataTable().nonempty() )
		{
			out << " {" << EOL;
			for( const auto & itRoutingData : getInputRoutingDataTable() )
			{
				out << TAB2;
				strPM(out, itRoutingData.getMachinePort());
				out << ";" << EOL;
			}
			out << TAB << "}" << EOL_FLUSH;
		}
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}



}
