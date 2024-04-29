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

#include "Router.h"

#include <fml/expression/AvmCode.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/InstanceOfPort.h>


namespace sep
{


/*
 * STATIC ATTRIBUTES
 */
Router Router::_NULL_;


/**
 * SETTER
 * mInputRoutingTable
 */
void Router::appendInputRouting(const InstanceOfPort & aPortInstance,
		const RoutingData & aRoutingData)
{
	RoutingData & oldRoutingData =
			getInputRouting( aPortInstance.getRouteOffset() );
	if( oldRoutingData.valid() )
	{
		if( (oldRoutingData.getMID() == aRoutingData.getMID())
			&& aRoutingData.hasBufferInstance() )
		{
			oldRoutingData.getBufferInstance().append(
					aRoutingData.getBufferInstance() );

			oldRoutingData.getBufferInstance().makeUnique();
		}
		else if( oldRoutingData.isMultiRoutingProtocol() )
		{
			oldRoutingData.appendManyCastRoutingData( aRoutingData );

//			AVM_OS_WARNING_ALERT
//					<< "appendInputRouting: Found a port < "
//					<< aPortInstance.getFullyQualifiedNameID()
//					<< " > with " << ComProtocol::to_string(
//							oldRoutingData.getProtocol() )
//					<< " routing<input> data in << "
//					<< getMachine().getFullyQualifiedNameID() << " >> !!!"
//					<< SEND_ALERT;
		}
		else
		{
			AVM_OS_WARNING_ALERT
					<< "appendInputRouting: Unexpected a port < "
					<< aPortInstance.getFullyQualifiedNameID()
					<< " > with another routing<input> data in << "
					<< getMachine().getFullyQualifiedNameID() << " >> !!!"
					<< SEND_ALERT;

			AVM_OS_LOG << "Input Routing Data of port : "
					<< aPortInstance.getFullyQualifiedNameID() << std::endl;
			oldRoutingData.toStream(AVM_OS_LOG << AVM_TAB_INDENT);
			AVM_OS_LOG << END_INDENT << std::endl;
		}
	}
	else
	{
		setInputRouting(aPortInstance.getRouteOffset(), aRoutingData);
	}
}

void Router::setInputRouting(const InstanceOfPort & aPortInstance,
		const RoutingData & aRoutingData) const
{
	if( getInputRoutingTable().get(aPortInstance.getRouteOffset()).valid() )
	{
		AVM_OS_WARNING_ALERT
				<< "setInputRouting: Unexpected a port < "
				<< aPortInstance.getFullyQualifiedNameID()
				<< " > with another routing<input> data in << "
				<< getMachine().getFullyQualifiedNameID() + " >> !!!"
				<< SEND_ALERT;

		AVM_OS_LOG << "Input Routing Data of port : "
				<< aPortInstance.getFullyQualifiedNameID() << std::endl;

		getInputRoutingTable().get(aPortInstance.getRouteOffset()).
				toStream(AVM_OS_LOG << AVM_TAB_INDENT);
		AVM_OS_LOG << END_INDENT << std::endl;
	}

	setInputRouting(aPortInstance.getRouteOffset(), aRoutingData);
}


/**
 * GETTER - SETTER
 * mOutputRoutingTable
 */
void Router::appendOutputRouting(const InstanceOfPort & aPortInstance,
		const RoutingData & aRoutingData)
{
	RoutingData & oldRoutingData =
			getOutputRouting( aPortInstance.getRouteOffset() );
	if( oldRoutingData.valid() )
	{
		if( (oldRoutingData.getMID() == aRoutingData.getMID())
			&& aRoutingData.hasBufferInstance() )
		{
			oldRoutingData.getBufferInstance().append(
					aRoutingData.getBufferInstance() );

			oldRoutingData.getBufferInstance().makeUnique();
		}
		else
		{
			AVM_OS_ERROR_ALERT
					<< "Unexpected a port < "
					<< aPortInstance.getFullyQualifiedNameID()
					<< " > with another routing<output> data in << "
					<< getMachine().getFullyQualifiedNameID() << " >> !!!"
					<< SEND_EXIT;

			AVM_OS_LOG << "Output Routing Data of port : "
					<< aPortInstance.getFullyQualifiedNameID() << std::endl;
			oldRoutingData.toStream(AVM_OS_LOG << AVM_TAB_INDENT);

			AVM_OS_LOG << END_INDENT << std::endl;
		}
	}
	else
	{
		setOutputRouting(aPortInstance.getRouteOffset(), aRoutingData);
	}
}

void Router::setOutputRouting(const InstanceOfPort & aPortInstance,
		const RoutingData & aRoutingData) const
{
	if( getOutputRoutingTable().get(aPortInstance.getRouteOffset()).valid() )
	{
		AVM_OS_ERROR_ALERT
				<< "Unexpected a port < "
				<< aPortInstance.getFullyQualifiedNameID()
				<< " > with another routing<output> data in << "
				<< getMachine().getFullyQualifiedNameID() << " >> !!!"
				<< SEND_EXIT;

		AVM_OS_LOG << "Output Routing Data of port : "
				<< aPortInstance.getFullyQualifiedNameID() << std::endl;

		getOutputRoutingTable().get(aPortInstance.getRouteOffset()).
				toStream(AVM_OS_LOG << AVM_TAB_INDENT);

		AVM_OS_LOG << END_INDENT << std::endl;
	}

	setOutputRouting(aPortInstance.getRouteOffset(), aRoutingData);
}


/**
 * TESTER
 */
bool Router::hasInputRouting(const InstanceOfPort & aPort) const
{
	return( aPort.getModifier().hasDirectionInput()
		&& (aPort.getRouteOffset() < getInputRoutingTable().size())
		&& getInputRouting(aPort.getRouteOffset()).valid()
		&& getInputRouting(aPort.getRouteOffset()).getPort().isTEQ(aPort) );
}

bool Router::hasOutputRouting(const InstanceOfPort & aPort) const
{
	return( aPort.getModifier().hasDirectionOutput()
		&& (aPort.getRouteOffset() < getOutputRoutingTable().size())
		&& getOutputRouting(aPort.getRouteOffset()).valid()
		&& getOutputRouting(aPort.getRouteOffset()).getPort().isTEQ(aPort) );
}


/**
 * Serialization
 */
void RouterElement::toStream(OutStream & os) const
{
	os << TAB << "router " << mMachine.getFullyQualifiedNameID();
	if( mMachine.isThis() )
	{
		os << "< " << mMachine.refExecutable().getFullyQualifiedNameID()
			<< " >";
	}
	AVM_DEBUG_REF_COUNTER(os);
	os << " {" << EOL;

	// routing table for INSTANCE
	if( mInputRoutingTable.nonempty() )
	{
		os << TAB << "input:" << EOL_INCR_INDENT;

		for( const auto & itInputRouting : mInputRoutingTable )
		{
			if( itInputRouting.valid() )
			{
				itInputRouting.toStream(os);
			}
			else
			{
				os << TAB << "RoutingData<null>" << EOL;
			}
		}
		os << DECR_INDENT;
	}

	if( mOutputRoutingTable.nonempty() )
	{
		os << TAB << "output:" << EOL_INCR_INDENT;

		for( const auto & itOutputRouting : mOutputRoutingTable )
		{
			if( itOutputRouting.valid() )
			{
				itOutputRouting.toStream(os);
			}
			else
			{
				os << TAB << "RoutingData<null>" << EOL;
			}
		}
		os << DECR_INDENT;
	}

	os << TAB << "}" << EOL << std::flush;
}


}
