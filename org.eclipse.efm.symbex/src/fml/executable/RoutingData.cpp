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

#include <fml/executable/InstanceOfConnect.h>
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
RoutingDataElement::RoutingDataElement(InstanceOfConnect * aConnector,
		InstanceOfMachine * aMachine, InstanceOfPort * aPort)
: Element( CLASS_KIND_T( RoutingData ) ),
mMID( aConnector->getMID() ),
mProtocol( aConnector->getProtocol() ),
mConnect( aConnector ),
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

void RoutingDataElement::toStream(OutStream & os) const
{
	os << TAB << "routing< "
			<< ComProtocol::to_string(mProtocol)
			<< " , mid:" << mMID<< " > ";
	if( getMachine()->isnotThis() )
	{
		os << ( mRuntimeRID.valid() ?  mRuntimeRID.strUniqId() :
				getMachine()->getFullyQualifiedNameID() ) << "->";
	}
	os << getPort()->getFullyQualifiedNameID() << " {";
	AVM_DEBUG_REF_COUNTER(os);
	os << EOL;

//	if( hasRuntimeRID() )
//	{
//		os << TAB2 << "rid#runtime = " << getRuntimeRID().str() << ";" << EOL;
//	}

	if( mConnect != NULL )
	{
		os << TAB2 << "connector = "
				<< mConnect->getFullyQualifiedNameID() << ";" <<  EOL;
	}

//	os << TAB2 << "machine = " << getMachine()->getFullyQualifiedNameID() << ";" <<  EOL;
//	os << TAB2 << "port = " << getPort()->getFullyQualifiedNameID() << ";" <<  EOL;

	if( mBufferInstance.nonempty() )
	{
		os << TAB2 << "buffer = [|";
		if( mBufferInstance.singleton() )
		{
			os << " " << str_header( mBufferInstance.first() ) << " ";
		}
		else
		{
			ListOfInstanceOfBuffer::const_iterator it = mBufferInstance.begin();
			ListOfInstanceOfBuffer::const_iterator itEnd = mBufferInstance.end();
			for( ; it != itEnd ; ++it )
			{
				os << EOL_TAB3 << str_header( *it );
			}
			os << EOL_TAB2;
		}
		os << "|];" << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;
}


}
