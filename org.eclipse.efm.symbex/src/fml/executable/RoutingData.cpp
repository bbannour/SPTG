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
#include "RoutingData.h"

#include <fml/executable/InstanceOfConnector.h>
#include <fml/executable/InstanceOfMachine.h>

#include <fml/infrastructure/ComProtocol.h>


namespace sep
{


/*
 * STATIC ATTRIBUTES
 */
RoutingData RoutingData::_NULL_;


/**
 * CONSTRUCTOR
 * Default
 */
RoutingDataElement::RoutingDataElement(
		std::size_t mid, const InstanceOfMachine & aMachine,
		const InstanceOfPort & aPort, ComProtocol::PROTOCOL_KIND aProtocol)
: Element( CLASS_KIND_T( RoutingData ) ),
mMID( mid ),

mProtocol( aProtocol ),
mConnector( InstanceOfConnector::nullref() ),
mMachinePort(aMachine, aPort),
mBufferInstance( ),
mRuntimeRID( )
{
	//!! NOTHING
}


RoutingDataElement::RoutingDataElement(const InstanceOfConnector & aConnector,
		const InstanceOfMachine & aMachine, const InstanceOfPort & aPort)
: Element( CLASS_KIND_T( RoutingData ) ),
mMID( aConnector.getMID() ),
mProtocol( aConnector.getProtocol() ),
mConnector( aConnector ),
mMachinePort(aMachine, aPort),
mBufferInstance( ),
mRuntimeRID( )
{
	//!! NOTHING
}


/**
 * Serialization
 */
std::string RoutingData::str() const
{
	StringOutStream oss;

	oss << "routing< " << ComProtocol::to_string( getProtocol() )
			<< " , mid:" << getMID()<< " >";

	if( hasRuntimeRID() )
	{
		oss << " " << getRuntimeRID().str();
	}

	if( getBufferInstance().nonempty() )
	{
		oss << " [| ";
		ListOfInstanceOfBuffer::const_iterator it = getBufferInstance().begin();
		for( ; it != getBufferInstance().end() ; ++it )
		{
			oss << str_header( *it ) << " ";
		}
		oss << "|]";
	}

	return( oss.str() );
}

void RoutingDataElement::toStreamPrefix(OutStream & out) const
{
	out << TAB << "routing< "
		<< ComProtocol::to_string(mProtocol)
		<< " , mid:" << mMID << " > ";

	if( getMachine().isnotThis() )
	{
		out << ( mRuntimeRID.valid() ?  mRuntimeRID.strUniqId() :
				getMachine().getFullyQualifiedNameID() ) << "->";
	}

	out << getPort().getFullyQualifiedNameID() << " {";
	AVM_DEBUG_REF_COUNTER(out);
	out << EOL;

//	if( hasRuntimeRID() )
//	{
//		out << TAB2 << "rid#runtime = " << getRuntimeRID().str() << ";" << EOL;
//	}

	out << TAB2 << "connector = " << mConnector.getFullyQualifiedNameID()
		<< ";" <<  EOL;

//	out << TAB2 << "machine = "
//		<< getMachine()->getFullyQualifiedNameID() << ";" <<  EOL;
//		<< TAB2 << "port = " << getPort()->getFullyQualifiedNameID() << ";"
//		<<  EOL;

	if( mBufferInstance.nonempty() )
	{
		out << TAB2 << "buffer = [|";
		if( mBufferInstance.singleton() )
		{
			out << " " << str_header( mBufferInstance.first() ) << " ";
		}
		else
		{
			for( const auto & itBuffer : mBufferInstance )
			{
				out << EOL_TAB3 << str_header( itBuffer );
			}
			out << EOL_TAB2;
		}
		out << "|];" << EOL;
	}

	out << std::flush;
}


void RoutingData::toStream(OutStream & out) const
{
	if( base_this_type::mPTR != nullptr )
	{
		base_this_type::mPTR->toStreamPrefix( out );

		if( mManyCastRoutingData.nonempty() )
		{
			out << EOL_INCR_INDENT;
			for( const auto & itManyRoutingData : mManyCastRoutingData )
			{
				itManyRoutingData.toStream(out);
			}
			out << DECR_INDENT;
		}

		out << TAB << "}" << EOL_FLUSH;
	}
	else
	{
		out << "RoutingData<null>" << std::flush;
	}
}



}
