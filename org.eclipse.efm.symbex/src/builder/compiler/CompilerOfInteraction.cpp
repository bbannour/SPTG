/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 sept. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "CompilerOfInteraction.h"

#include <builder/compiler/SymbolTable.h>
#include <builder/compiler/Compiler.h>

#include <fml/common/ModifierElement.h>

#include <fml/lib/IComPoint.h>

#include <fml/builtin/Identifier.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfBuffer.h>
#include <fml/executable/InstanceOfConnect.h>
#include <fml/executable/InstanceOfData.h>
#include <fml/executable/InstanceOfMachine.h>
#include <fml/executable/Router.h>

#include <fml/infrastructure/Buffer.h>
#include <fml/infrastructure/Channel.h>
#include <fml/infrastructure/ComPoint.h>
#include <fml/infrastructure/ComProtocol.h>
#include <fml/infrastructure/ComRoute.h>
#include <fml/infrastructure/Connector.h>
#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/PropertyPart.h>

#include <fml/type/BaseTypeSpecifier.h>
#include <fml/type/TypeManager.h>

#include <fml/workflow/UniFormIdentifier.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
CompilerOfInteraction::CompilerOfInteraction(Compiler & aCompiler)
: BaseCompiler(aCompiler),
mNextRouteID( 0 ),
mNextConnectID( 0 )
{
	//!! NOTHING
}


/**
 *******************************************************************************
 * PRECOMPILATION
 *******************************************************************************
 */

/**
 * precompile
 * port
 */

BF CompilerOfInteraction::precompileParameter(
		ExecutableForm * aContainer, TableOfInstanceOfData & tableOfVariable,
		Variable * aParameter, avm_offset_t offset)
{
	// #bind parameter
	if( aParameter->getModifier().hasNatureParameterBind() )
	{
		InstanceOfData * bindInstance = new InstanceOfData(
				IPointerDataNature::POINTER_STANDARD_NATURE,
				aContainer, aParameter, TypeManager::UNIVERSAL,
				offset, aParameter->getModifier() );
		if( aParameter->getNameID().empty() )
		{
			bindInstance->setNameID( OSS() << "$" << offset );
		}
		else
		{
			bindInstance->setNameID( aParameter->getNameID() );
		}
		bindInstance->setValue( aParameter->getValue() );

		return( BF( bindInstance ) );
	}

	// variable parameter
	else if( aParameter->getModifier().hasNatureParameter() )
	{
		TypeSpecifier aTypeSpecifier =
				compileTypeSpecifier(aContainer, aParameter->getType());

		InstanceOfData * paramInstance = new InstanceOfData(
				IPointerDataNature::POINTER_STANDARD_NATURE, aContainer,
				aParameter, aTypeSpecifier, offset,
				aParameter->getModifier() );
		if( aParameter->getNameID().empty() )
		{
			paramInstance->setNameID( OSS() << "$" << offset );
		}
		else
		{
			paramInstance->setNameID( aParameter->getNameID() );
		}
		paramInstance->setValue( aParameter->getValue() );

		return( BF( paramInstance ) );
	}

	return( BF::REF_NULL );
}


void CompilerOfInteraction::precompileComPoint(ExecutableForm * aContainer,
		PropertyPart & theDeclaration, TableOfInstanceOfData & tableOfVariable)
{
	PropertyPart::TableOfPort listOfInputPort;
	PropertyPart::TableOfPort listOfInoutPort;
	PropertyPart::TableOfPort listOfOutputPort;

	BF aParameter;
	TableOfVariable::const_raw_iterator itParam;
	TableOfVariable::const_raw_iterator endParam;

	avm_size_t inoutPortCount = 0;

	// Classification of signals
	PropertyPart::TableOfSignal::const_raw_iterator its =
			theDeclaration.getSignals().begin();
	PropertyPart::TableOfSignal::const_raw_iterator endIts =
			theDeclaration.getSignals().end();
	for( ; its != endIts ; ++its )
	{
		if( (its)->getModifier().isDirectionInput() )
		{
			listOfInputPort.append( *its );
		}
		else if( (its)->getModifier().isDirectionInout() )
		{
			listOfInoutPort.append( *its );
			++inoutPortCount;
		}
		else if( (its)->getModifier().isDirectionOutput() )
		{
			listOfOutputPort.append( *its );
		}
	}

	aContainer->setMessageSignalCount( theDeclaration.getSignals().size() );

	// Classification of ports
	PropertyPart::TableOfPort::const_raw_iterator itp =
			theDeclaration.getPorts().begin();
	PropertyPart::TableOfPort::const_raw_iterator endItp =
			theDeclaration.getPorts().end();
	for( ; itp != endItp ; ++itp )
	{
		if( (itp)->getModifier().isDirectionInput() )
		{
			listOfInputPort.append( *itp );
		}
		else if( (itp)->getModifier().isDirectionInout() )
		{
			listOfInoutPort.append( *itp );
			++inoutPortCount;
		}
		else if( (itp)->getModifier().isDirectionOutput() )
		{
			listOfOutputPort.append( *itp );
		}
	}

	// Pre-compilation of ports
	precompileComPoint(aContainer,
			listOfInoutPort, 0, tableOfVariable);

	precompileComPoint(aContainer,
			listOfInputPort, inoutPortCount, tableOfVariable);

	precompileComPoint(aContainer,
			listOfOutputPort, inoutPortCount, tableOfVariable);
}


void CompilerOfInteraction::precompileComPoint(ExecutableForm * aContainer,
		const PropertyPart::TableOfPort & listOfComPoint,
		avm_size_t ioPortOffset, TableOfInstanceOfData & tableOfVariable)
{
	InstanceOfPort * newPortInstance = NULL;

	BF aParameter;
	TableOfVariable::const_raw_iterator itParam;
	TableOfVariable::const_raw_iterator endParam;

	avm_offset_t typeOffset = 0;

	PropertyPart::TableOfPort::const_raw_iterator it = listOfComPoint.begin();
	PropertyPart::TableOfPort::const_raw_iterator endIt = listOfComPoint.end();
	for( avm_offset_t offset = ioPortOffset ; it != endIt ; ++it , ++offset )
	{
		newPortInstance = new InstanceOfPort(aContainer, (it), offset,
				(it)->getParameters().size(), (it)->getComPointNature());

		getSymbolTable().addPortInstance(
				aContainer->savePort(newPortInstance) );

		if( newPortInstance->isSignal() )
		{
			newPortInstance->setRouteOffset( mNextRouteID++ );
		}

		itParam = (it)->getParameters().begin();
		endParam = (it)->getParameters().end();
		for( typeOffset = 0 ; itParam != endParam ; ++itParam , ++typeOffset )
		{
			aParameter = precompileParameter(aContainer,
					tableOfVariable, (itParam), typeOffset);
			newPortInstance->setParameter(typeOffset, aParameter);
		}
	}
}



void CompilerOfInteraction::precompileChannel(ExecutableForm * aContainer,
		PropertyPart & theDeclaration, TableOfInstanceOfData & tableOfVariable)
{
	InstanceOfPort * newInstanceOfChannel;
	InstanceOfPort * newInstanceOfPort;

	PropertyPart::const_owned_iterator it;
	PropertyPart::const_owned_iterator endIt;

	PropertyPart::TableOfChannel::const_raw_iterator itChannel =
			theDeclaration.getChannels().begin();
	PropertyPart::TableOfChannel::const_raw_iterator endChannel =
			theDeclaration.getChannels().end();
	avm_offset_t offset = 0;
	for( ; itChannel != endChannel ; ++itChannel, ++offset )
	{
		newInstanceOfChannel = InstanceOfPort::newChannel(
				aContainer, (itChannel), offset);

		aContainer->saveChannel(newInstanceOfChannel);

		if( (itChannel)->hasContents() )
		{
			it = (itChannel)->getContents()->owned_begin();
			endIt = (itChannel)->getContents()->owned_end();
			for( ; it != endIt ; ++it )
			{
				// case of Signal
				if( (*it).is< Signal >() )
				{
					const Symbol & aPort = getSymbolTable().searchPortInstance(
							(*it).to_ptr< Port >()->getSignalModel() );
					if( aPort.valid() )
					{
						newInstanceOfPort = new InstanceOfPort(
								aContainer, (*it).to_ptr< Port >(),
								newInstanceOfChannel, aPort.rawPort() );

						newInstanceOfChannel->appendContent(
								Symbol(newInstanceOfPort) );
					}
				}

				else if( (*it).is< Variable >() )
				{

				}
			}
		}
	}
}


/**
 * precompile
 * buffer
 */
void CompilerOfInteraction::precompileBuffer(
		ExecutableForm * aContainer, Buffer * aBuffer)
{
	InstanceOfBuffer * newBufferInstance = new InstanceOfBuffer(
			aContainer, aBuffer, aContainer->getBuffer().size());

	getSymbolTable().addBufferInstance(
			aContainer->saveBuffer(newBufferInstance) );
}






/**
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 * COMPILATION
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 *******************************************************************************
 */


void CompilerOfInteraction::compilePort(ExecutableForm * anExecutable)
{
	TableOfSymbol::const_iterator itPort = anExecutable->getPort().begin();
	TableOfSymbol::const_iterator endPort = anExecutable->getPort().end();
	for( ; itPort != endPort ; ++itPort )
	{
		compilePort(anExecutable, (*itPort).port());
	}
}

void CompilerOfInteraction::compilePort(ExecutableForm * anExecutable,
		const InstanceOfPort & aPortInstance)
{
	ArrayOfBF::const_iterator it = aPortInstance.getParameters().begin();
	ArrayOfBF::const_iterator endIt = aPortInstance.getParameters().end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).is< InstanceOfData >() )
		{
			InstanceOfData * aVar = (*it).to_ptr< InstanceOfData >();

			// #bind parameter
			if( aVar->getModifier().hasNatureParameterBind()
				&& aVar->hasValue() )
			{
				aVar->setValue( mAvmcodeCompiler.decode_compileExpression(
						anExecutable, aVar->getValue()) );
			}

			// variable parameter, optional default value
			else if( aVar->getModifier().hasNatureParameter()
					&& aVar->hasValue()
					&& (not aVar->getValue().isNumeric()) )
			{
				aVar->setValue( mAvmcodeCompiler.decode_compileExpression(
						anExecutable, aVar->getValue()) );
			}
		}
	}
}


/**
 *******************************************************************************
 * TOOLS FOR ROUTER CREATION
 *******************************************************************************
 */

Router CompilerOfInteraction::newMachineRouter(InstanceOfMachine * aMachine)
{
	Router aRouter(aMachine, mNextRouteID, mNextRouteID);

	ExecutableForm * anExecutable = aMachine->getExecutable();

	TableOfSymbol::iterator itPort = anExecutable->getPort().begin();
	TableOfSymbol::iterator endPort = anExecutable->getPort().end();
	for( ; itPort != endPort ; ++itPort )
	{
		if( (*itPort).port().isPort() )
		{
			// the route offset of local port w.r.t. global route offset
			(*itPort).setRouteOffset( mNextRouteID + (*itPort).getOffset() -
					anExecutable->getMessageSignalCount() );

			if( (*itPort).getModifier().hasDirectionInput() )
			{
				aRouter.appendInputRouting( RoutingData::_NULL_ );
			}
			// NO ELSE because of INOUT PORT
			if( (*itPort).getModifier().hasDirectionOutput() )
			{
				aRouter.appendOutputRouting( RoutingData::_NULL_ );
			}
		}

		else// if( (*itPort).isSignal() )
		{
			//!! NOTHING
		}
	}

	return( aRouter );
}


Router CompilerOfInteraction::addMachineModelRouter(
		ExecutableForm * theExecutable, InstanceOfMachine * aMachine)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aMachine->getOffset() == 0 )
			<< "Unexpected the first machine model "
				"for router with offset > 0 !!!"
			<< SEND_EXIT;

	Router aRouter = newMachineRouter(aMachine);

	theExecutable->appendRouter4Model( aRouter );

	return( aRouter );
}



/**
 * compile
 * statemachine interaction
 */
void CompilerOfInteraction::compileCommunication(ExecutableForm * theExecutable,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	const Machine * aMachine = theExecutable->getAstMachine();

	if( aMachine->hasInteraction() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable->hasInstanceStaticThis() )
				<< "Unexpected communicated Machine without submachine THIS !!!"
				<< SEND_EXIT;

		avm_size_t nbComMachineCount = 0;

		TableOfRouter & theTableOfRouter4Instance =
				theExecutable->getRouters4Instance();

		// Attention: the offset of routing table of an instance machine is
		// the same than the offset of this instance
		TableOfSymbol::const_iterator itMachine =
				theExecutable->getInstanceStatic().begin();
		TableOfSymbol::const_iterator endMachine =
				theExecutable->getInstanceStatic().end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).getExecutable()->hasPort() )
			{
				++nbComMachineCount;
				theTableOfRouter4Instance.append(
						newMachineRouter((*itMachine).rawMachine()) );
//@debug:
//				AVM_OS_TRACE << "compileCommunication :> INIT "
//						<< str_header( theExecutable ) << std::endl;
//				theRouterTable->last()->toStream(AVM_OS_TRACE);
			}
			else if( (*itMachine).getAstMachine()->hasInteraction() )
			{
				++nbComMachineCount;
				theTableOfRouter4Instance.append(
						newMachineRouter((*itMachine).rawMachine()) );
//@debug:
//				AVM_OS_TRACE << "compileCommunication :> INIT "
//						<< str_header( theExecutable ) << std::endl;
//				theRouterTable->last()->toStream(AVM_OS_TRACE);
			}
			else
			{
				theTableOfRouter4Instance.append( Router::_NULL_ );
			}
		}

		// For MACHINE MODEL
		TableOfRouter & theTableOfRouter4Model =
				theExecutable->getRouters4Model();

		// Router for instance machine THIS
		theTableOfRouter4Model.append( theExecutable->getRouter4This() );

		itMachine = theExecutable->instance_model_begin();
		endMachine = theExecutable->instance_model_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).getExecutable()->hasPort() )
			{
				++nbComMachineCount;
				theTableOfRouter4Model.append(
						newMachineRouter((*itMachine).rawMachine()) );
//@debug:
//				AVM_OS_TRACE << "compileCommunication :> INIT "
//						<< str_header( theExecutable ) << std::endl;
//				theRouterTable->last()->toStream(AVM_OS_TRACE);
			}
			else if( (*itMachine).getAstMachine()->hasInteraction() )
			{
				++nbComMachineCount;
				theTableOfRouter4Model.append(
						newMachineRouter((*itMachine).rawMachine()) );
//@debug:
//				AVM_OS_TRACE << "compileCommunication :> INIT "
//						<< str_header( theExecutable ) << std::endl;
//				theRouterTable->last()->toStream(AVM_OS_TRACE);
			}
			else
			{
				theTableOfRouter4Model.append( Router::_NULL_ );
			}
		}

		if( nbComMachineCount > 0 )
		{
			compileConnector(theExecutable,
					hasUpdateBuffer, hasSynchronizeMachine);

			postCompileCommunication(theExecutable);
		}
		else
		{
			theExecutable->getRouters4Instance().clear();

			theExecutable->getRouters4Model().clear();
		}
	}

	else if( aMachine->hasPortSignal()
			&& ( aMachine->getSpecifier().isComponentSystem()
				|| (not aMachine->getContainerMachine()->hasInteraction()) ) )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable->hasInstanceStaticThis() )
				<< "Unexpected communicated Machine without submachine THIS !!!"
				<< SEND_EXIT;

		Router bfRouter = newMachineRouter(
				theExecutable->getInstanceStaticThis().rawMachine());

		theExecutable->appendRouter4Instance( bfRouter );

		if( not aMachine->getSpecifier().isComponentSystem() )
		{
			theExecutable->appendRouter4Model( bfRouter );
		}

//@debug:
//		AVM_OS_TRACE << "compileCommunication :> INIT "
//				<< str_header( aMachine ) << std::endl;
//		theRouterTable->last()->toStream(AVM_OS_TRACE);

		postCompileCommunication(theExecutable);
	}
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnector(ExecutableForm * theExecutable,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	const Machine * aMachine = theExecutable->getAstMachine();

	InstanceOfConnect * ioc = NULL;

	InteractionPart::const_connector_iterator itConnector;
	InteractionPart::const_connector_iterator endConnector;

	const InteractionPart * theInteractionPart = aMachine->getInteraction();
	if( theInteractionPart != NULL )
	{
		itConnector  = theInteractionPart->connector_begin();
		endConnector = theInteractionPart->connector_end();
		for( ; itConnector != endConnector ; ++itConnector )
		{
			ioc = new InstanceOfConnect( theExecutable,
					(itConnector), theExecutable->getConnect().size(),
					(itConnector)->getProtocol(), (itConnector)->getCast() );

			getSymbolTable().addConnectInstance(
					theExecutable->saveConnect(ioc) );

			////////////////////////////////////////////////////////////////////
			// For PORT
			if( (itConnector)->isPort() )
			{
				compileConnector(theExecutable, (itConnector), ioc,
						hasSynchronizeMachine, hasUpdateBuffer);
			}

			////////////////////////////////////////////////////////////////////
			// For MESSAGE OR SIGNAL
			else if( (itConnector)->isSignal() )
			{
				compileRoute(theExecutable, (itConnector), ioc,
						hasSynchronizeMachine, hasUpdateBuffer);
			}
		}
	}
}



void CompilerOfInteraction::compileConnector(ExecutableForm * theExecutable,
		Connector * aConnector, InstanceOfConnect * ioc,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	// One unique Connector ID per connection!
	ioc->setMID( ++mNextConnectID );
	switch( aConnector->getProtocol() )
	{
		case ComProtocol::PROTOCOL_BUFFER_KIND:
		{
			compileConnectorBuffer(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_RDV_KIND:
		case ComProtocol::PROTOCOL_MULTIRDV_KIND:
		{
			hasSynchronizeMachine = true;
			compileConnectorSynchronous(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_FLOW_KIND:
		{
			hasSynchronizeMachine = true;
			compileConnectorFlow(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:
		{
			hasUpdateBuffer = true;
			compileConnectorBroadcast(theExecutable, ioc);
			break;
		}


		case ComProtocol::PROTOCOL_TRANSFERT_KIND:
		{
			compileConnectorTransfert(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
		{
			compileConnectorEnvironment(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		case ComProtocol::PROTOCOL_ANYCAST_KIND:
		{
			compileConnectorRoutingCast(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			// ERROR REPORTING
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unexpected for the connection<port> the protocol << "
					<< aConnector->strProtocolCast(true) << " >>"
					<< std::endl;

			break;
		}
	}
}

void CompilerOfInteraction::compileRoute(ExecutableForm * theExecutable,
		Connector * aConnector, InstanceOfConnect * ioc,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	switch( aConnector->getProtocol() )
	{
		case ComProtocol::PROTOCOL_BUFFER_KIND:
		{
			compileRouteBuffer(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_RDV_KIND:
		case ComProtocol::PROTOCOL_MULTIRDV_KIND:
		{
			hasSynchronizeMachine = true;
			compileRouteSynchronous(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:
		{
			hasUpdateBuffer = true;
			compileRouteBroadcast(theExecutable, ioc);
			break;
		}


		case ComProtocol::PROTOCOL_TRANSFERT_KIND:
		{
			compileRouteTransfert(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
		{
			compileRouteEnvironment(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		case ComProtocol::PROTOCOL_ANYCAST_KIND:
		{
			compileRouteRoutingCast(theExecutable, ioc);
			break;
		}

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			// ERROR REPORTING
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unexpected for the connection<message|signal> "
							"the protocol << "
					<< aConnector->strProtocolCast(true) << " >>"
					<< std::endl;

			break;
		}
	}
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT BROADCAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorBroadcast(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT BROADCAST" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;

	if( aConnector->hasBuffer() )
	{
		buffer = aConnector->getBuffer();

		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(
					theExecutable, buffer, theExecutable->getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable->saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					theExecutable, buffer).rawBuffer();
		}
	}
	else if( aConnector->hasBufferUfid() )
	{
		theBufferInstance =
				getSymbolTable().searchBufferInstanceByQualifiedNameID(
					theExecutable, aConnector->strBufferUfid()).rawBuffer();

		if( theBufferInstance == NULL )
		{
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unfound in the COM POINT the buffer instance < "
					<< aConnector->strBufferUfid() << " > !" << std::endl;
		}
	}
	else //if( buffer == NULL )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable,	NULL, theExecutable->getBuffer().size(),
				TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable->saveBuffer(theBufferInstance) );
	}


	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// for buffer port
				if( theBufferInstance != NULL )
				{
					theRoutingData.appendBuffer(theBufferInstance);
				}

				if( (*itComRoute)->hasProtocol() )
				{
					// TODO for other COM_PROTOCOL
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT BROADCAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT BUFFER
 *******************************************************************************
 */

static void bufferCompletion(
		List< RoutingData > & listOfOutRoutingData,
		List< RoutingData > & listOfInRoutingData)
{
	List< RoutingData >::iterator inRD;
	List< RoutingData >::iterator outRD;

	bool hasntBuffer;

	inRD = listOfInRoutingData.begin();
	for( ; inRD != listOfInRoutingData.end() ; ++inRD )
	{
		hasntBuffer = inRD->getBufferInstance().empty();

		outRD = listOfOutRoutingData.begin();
		for( ; outRD != listOfOutRoutingData.end() ; ++outRD )
		{
			if( hasntBuffer && outRD->getBufferInstance().nonempty() )
			{
				inRD->getBufferInstance().append(
						outRD->getBufferInstance() );
			}
		}

		inRD->getBufferInstance().makeUnique();
	}

	outRD = listOfOutRoutingData.begin();
	for( ; outRD != listOfOutRoutingData.end() ; ++outRD )
	{
		hasntBuffer = (outRD)->getBufferInstance().empty();

		inRD = listOfInRoutingData.begin();
		for( ; inRD != listOfInRoutingData.end() ; ++inRD )
		{
			if( hasntBuffer && (inRD)->getBufferInstance().nonempty() )
			{
				(outRD)->getBufferInstance().append(
						(inRD)->getBufferInstance() );
			}
		}

		(outRD)->getBufferInstance().makeUnique();
	}
}


void CompilerOfInteraction::compileConnectorBuffer(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT BUFFER" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;
	InstanceOfBuffer * localBufferInstance = NULL;

	if( aConnector->hasBuffer() )
	{
		buffer = aConnector->getBuffer();

		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(theExecutable,
					buffer, theExecutable->getBuffer().size() );

			getSymbolTable().addBufferInstance(
					theExecutable->saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					theExecutable, buffer).rawBuffer();
		}
	}
	else if( aConnector->hasBufferUfid() )
	{
		theBufferInstance =
				getSymbolTable().searchBufferInstanceByQualifiedNameID(
					theExecutable, aConnector->strBufferUfid()).rawBuffer();

		if( theBufferInstance == NULL )
		{
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unfound in the COM POINT the buffer instance < "
					<< aConnector->strBufferUfid() << " > !" << std::endl;
		}
	}
	else //if( buffer == NULL )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable,	NULL, theExecutable->getBuffer().size(),
				TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable->saveBuffer(theBufferInstance) );
	}

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				if( theBufferInstance != NULL )
				{
					// for buffer port
					theRoutingData.appendBuffer(theBufferInstance);
				}

				// for buffer port
				if( not (*itComRoute)->hasProtocol() )
				{
					continue;
				}

				switch( (*itComRoute)->getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						localBufferInstance = theBufferInstance;

						if( (*itComRoute)->hasBuffer() )
						{
							buffer = (*itComRoute)->getBuffer();
							if( buffer->isAnonymID() )
							{
								localBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable->getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable->saveBuffer(
											localBufferInstance) );
							}
							else
							{
								localBufferInstance = getSymbolTable().
									searchBufferInstance(
										theExecutable, buffer).rawBuffer();
							}
						}
						else if( (*itComRoute)->hasBufferUfid() )
						{
							localBufferInstance = getSymbolTable().
								searchBufferInstanceByQualifiedNameID(
									theExecutable,
									(*itComRoute)->strBufferUfid()).rawBuffer();

							if( localBufferInstance == NULL )
							{
								incrErrorCount();
								aConnector->errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< aConnector->strBufferUfid() << " > !"
										<< std::endl;
							}
						}

						if( localBufferInstance != NULL )
						{
							theRoutingData.appendBuffer(localBufferInstance);
						}
						else
						{
							// TODO for other ERROR
						}

						break;
					}

					default:
					{
						// TODO for other COM_PROTOCOL
						break;
					}
				}

				// list for update all buffer and port connector list
				if( (*itComRoute)->getModifier().isDirectionOutput() )
				{
					listOfOutRoutingData.append(theRoutingData);
				}
				else
				{
					listOfInRoutingData.append(theRoutingData);
				}
			}
		}
	}


	// buffer completion
	bufferCompletion(listOfOutRoutingData, listOfInRoutingData);


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT BUFFER"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT ROUTING CAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorRoutingCast(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT ROUTING CAST" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// list for update input buffer and port connector list
				listOfOutRoutingData.append(theRoutingData);

				// for buffer port
				if( not (*itComRoute)->hasProtocol() )
				{
					continue;
				}

				switch( (*itComRoute)->getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						if( (*itComRoute)->hasBuffer() )
						{
							buffer = (*itComRoute)->getBuffer();
							if( buffer->isAnonymID() )
							{
								theBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable->getBuffer().size());

								getSymbolTable().addBufferInstance(
										theExecutable->saveBuffer(
												theBufferInstance) );
							}
							else
							{
								theBufferInstance = getSymbolTable().
									searchBufferInstance(
											theExecutable, buffer).rawBuffer();
							}
						}
						else if( (*itComRoute)->hasBufferUfid() )
						{
							theBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									(*itComRoute)->strBufferUfid()).rawBuffer();

							if( theBufferInstance == NULL )
							{
								incrErrorCount();
								aConnector->errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< (*itComRoute)->strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( theBufferInstance != NULL )
						{
							theRoutingData.appendBuffer(theBufferInstance);
						}
						else
						{
							// TODO for other ERROR
						}

						break;
					}

					case ComProtocol::PROTOCOL_MULTICAST_KIND:
					{
						break;
					}
					case ComProtocol::PROTOCOL_UNICAST_KIND:
					{
						break;
					}
					case ComProtocol::PROTOCOL_ANYCAST_KIND:
					{
						break;
					}
					default:
					{
						// TODO for other COM_PROTOCOL
						break;
					}
				}

				// list for update all buffer and port connector list
				if( (*itComRoute)->getModifier().isDirectionOutput() )
				{
					listOfOutRoutingData.append(theRoutingData);
				}
				else
				{
					listOfInRoutingData.append(theRoutingData);
				}
			}
		}
	}


	// buffer completion
	bufferCompletion(listOfOutRoutingData, listOfInRoutingData);


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << TAB_DECR_INDENT
	<< "END COMPILE INTERACTION CONNECT ROUTING CAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT SYNCHRONOUS
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorSynchronous(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT SYNCHRONOUS"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		if( (*itComRoute)->hasCast() )
		{
			if( (*itComRoute)->getModifier().isDirectionOutput() )
			{
				ioc->getOutputComRouteData().setCast((*itComRoute)->getCast());
			}
			else
			{
				ioc->getInputComRouteData().setCast((*itComRoute)->getCast());
			}
		}

		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			if( (*itComRoute)->hasProtocol() )
			{
				// TODO for other COM_PROTOCOL
			}
		}
	}

	if( ioc->getProtocol() == ComProtocol::PROTOCOL_MULTIRDV_KIND )
	{
		if( (not ioc->getOutputComRouteData().hasCast()) &&
				ioc->getOutputComRouteData().getMachinePorts().singleton() )
		{
			ioc->getOutputComRouteData().setCast(
					ComProtocol::PROTOCOL_UNICAST_KIND );
		}

		if( (not ioc->getInputComRouteData().hasCast()) &&
				ioc->getInputComRouteData().getMachinePorts().singleton() )
		{
			ioc->getInputComRouteData().setCast(
					ComProtocol::PROTOCOL_UNICAST_KIND );
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT SYNCHRONOUS"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT FLOW
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorFlow(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT FLOW"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			if( (*itComRoute)->hasProtocol() )
			{
				// TODO for other COM_PROTOCOL
			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT FLOW"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT TRANSFERT
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorTransfert(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT TRANSFERT"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( theRoutingData.getComPoint()->is< OutputComPoint >() )
//				{
//					theExecutable->getRouter4Instance(
//						theInstanceStatic->getOffset())->setOutputRouting(
//								theComPointInstance, theRoutingData);
//					ioc->getOutputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//
//				if( theRoutingData.getComPoint()->is< InputComPoint >() )
//				{
//					theExecutable->getRouter4Instance(
//						theInstanceStatic->getOffset())->setInputRouting(
//								theComPointInstance, theRoutingData);
//					ioc->getInputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT TRANSFERT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}

/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT ENVIRONMENT
 *******************************************************************************
 */

void CompilerOfInteraction::compileConnectorEnvironment(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT ENVIRONMENT"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// ERROR REPORTING
				if( theRoutingData.getPort()->getModifier().isnotDirectionKind(
						(*itComRoute)->getModifier().getDirectionKind() )
					&& (not theRoutingData.getPort()->
							getModifier().isDirectionInout()) )
				{
					incrErrorCount();
					AVM_OS_WARN << (*itComRoute)->errorLocation(aConnector)
						<< "Unexpected a "
						<< theRoutingData.getPort()->getModifier().strDirection()
						<< " PORT << "
						<< theRoutingData.getPort()->getFullyQualifiedNameID()
						<< " >> in an "
						<< (*itComRoute)->getModifier().strDirection()
						<< " BUS << " << aConnector->getFullyQualifiedNameID()
						<< " >>" << std::endl;
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT ENVIRONMENT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}








/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT BROADCAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteBroadcast(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT BROADCAST"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;

	if( aConnector->hasBuffer() )
	{
		buffer = aConnector->getBuffer();

		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(
					theExecutable, buffer, theExecutable->getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable->saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					theExecutable, buffer).rawBuffer();
		}
	}
	else if( aConnector->hasBufferUfid() )
	{
		theBufferInstance =
			getSymbolTable().searchBufferInstanceByQualifiedNameID(
				theExecutable, aConnector->strBufferUfid()).rawBuffer();

		if( theBufferInstance == NULL )
		{
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unfound in the COM POINT the buffer instance < "
					<< aConnector->strBufferUfid() << " > !" << std::endl;
		}
	}
	else if( buffer == NULL )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable,	buffer, theExecutable->getBuffer().size(),
				TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable->saveBuffer(theBufferInstance) );
	}


	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// for buffer port
				if( theBufferInstance != NULL )
				{
					theRoutingData.appendBuffer(theBufferInstance);
				}

				if( (*itComRoute)->hasProtocol() )
				{
					// TODO for other COM_PROTOCOL
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT BROADCAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT BUFFER
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteBuffer(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT BUFFER" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;
	InstanceOfBuffer * localBufferInstance = NULL;

	if( aConnector->hasBuffer() )
	{
		buffer = aConnector->getBuffer();
		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(
					theExecutable, buffer, theExecutable->getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable->saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					theExecutable, buffer).rawBuffer();
		}
	}
	else if( aConnector->hasBufferUfid() )
	{
		theBufferInstance =
			getSymbolTable().searchBufferInstanceByQualifiedNameID(
				theExecutable, aConnector->strBufferUfid()).rawBuffer();

		if( theBufferInstance == NULL )
		{
			incrErrorCount();
			aConnector->errorLocation(AVM_OS_WARN)
					<< "Unfound in the COM POINT the buffer instance < "
					<< aConnector->strBufferUfid() << " > !" << std::endl;
		}
	}
	else if( buffer == NULL )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable,	buffer, theExecutable->getBuffer().size(),
				TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable->saveBuffer(theBufferInstance) );
	}

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				if( theBufferInstance != NULL )
				{
					// for buffer port
					theRoutingData.appendBuffer(theBufferInstance);
				}

				// for buffer port
				if( not (*itComRoute)->hasProtocol() )
				{
					continue;
				}

				switch( (*itComRoute)->getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						localBufferInstance = theBufferInstance;

						if( (*itComRoute)->hasBuffer() )
						{
							buffer = (*itComRoute)->getBuffer();

							if( buffer->isAnonymID() )
							{
								localBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable->getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable->saveBuffer(
											localBufferInstance) );
							}
							else
							{
								localBufferInstance = getSymbolTable().
									searchBufferInstance(theExecutable, buffer).
										rawBuffer();
							}
						}
						else if( (*itComRoute)->hasBufferUfid() )
						{
							localBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									(*itComRoute)->strBufferUfid()).rawBuffer();

							if( localBufferInstance == NULL )
							{
								incrErrorCount();
								aConnector->errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< (*itComRoute)->strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( localBufferInstance != NULL )
						{
							theRoutingData.appendBuffer(localBufferInstance);
						}
						else
						{
							// TODO for other ERROR
						}

						break;
					}

					default:
					{
						// TODO for other COM_PROTOCOL
						break;
					}
				}

				// list for update all buffer and port connector list
				if( (*itComRoute)->getModifier().isDirectionOutput() )
				{
					listOfOutRoutingData.append(theRoutingData);
				}
				else
				{
					listOfInRoutingData.append(theRoutingData);
				}
			}
		}
	}


	// buffer completion
	bufferCompletion(listOfOutRoutingData, listOfInRoutingData);


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT BUFFER"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT ROUTING CAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteRoutingCast(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT ROUTING CAST"
			<< std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	Buffer * buffer = NULL;
	InstanceOfBuffer * theBufferInstance = NULL;

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// list for update input buffer and port connector list
				listOfOutRoutingData.append(theRoutingData);

				// for buffer port
				if( not (*itComRoute)->hasProtocol() )
				{
					continue;
				}

				switch( (*itComRoute)->getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						if( (*itComRoute)->hasBuffer() )
						{
							buffer = (*itComRoute)->getBuffer();

							if( buffer->isAnonymID() )
							{
								theBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable->getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable->saveBuffer(theBufferInstance));
							}
							else
							{
								theBufferInstance = getSymbolTable().
									searchBufferInstance(theExecutable, buffer).
										rawBuffer();
							}
						}
						else if( (*itComRoute)->hasBufferUfid() )
						{
							theBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									(*itComRoute)->strBufferUfid()).rawBuffer();

							if( theBufferInstance == NULL )
							{
								incrErrorCount();
								aConnector->errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< (*itComRoute)->strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( theBufferInstance != NULL )
						{
							theRoutingData.appendBuffer(theBufferInstance);
						}
						else
						{
							// TODO for other ERROR
						}

						break;
					}

					case ComProtocol::PROTOCOL_MULTICAST_KIND:
					{
						break;
					}
					case ComProtocol::PROTOCOL_UNICAST_KIND:
					{
						break;
					}
					case ComProtocol::PROTOCOL_ANYCAST_KIND:
					{
						break;
					}
					default:
					{
						// TODO for other COM_PROTOCOL
						break;
					}
				}

				// list for update all buffer and port connector list
				if( (*itComRoute)->getModifier().isDirectionOutput() )
				{
					listOfOutRoutingData.append(theRoutingData);
				}
				else
				{
					listOfInRoutingData.append(theRoutingData);
				}
			}
		}
	}


	// buffer completion
	bufferCompletion(listOfOutRoutingData, listOfInRoutingData);


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT ROUTING CAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT SYNCHRONOUS
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteSynchronous(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT SYNCHRONOUS" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		if( (*itComRoute)->hasCast() )
		{
			if( (*itComRoute)->getModifier().isDirectionOutput() )
			{
				ioc->getOutputComRouteData().setCast(
						(*itComRoute)->getCast() );
			}
			else
			{
				ioc->getInputComRouteData().setCast(
						(*itComRoute)->getCast() );
			}
		}

		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( (*itComRoute)->hasProtocol() )
//				{
//					// TODO for other COM_PROTOCOL
//				}
//			}
		}
	}

	if( ioc->getProtocol() == ComProtocol::PROTOCOL_MULTIRDV_KIND )
	{
		if( (not ioc->getOutputComRouteData().hasCast()) &&
				ioc->getOutputComRouteData().getMachinePorts().singleton() )
		{
			ioc->getOutputComRouteData().setCast(
					ComProtocol::PROTOCOL_UNICAST_KIND );
		}

		if( (not ioc->getInputComRouteData().hasCast()) &&
				ioc->getInputComRouteData().getMachinePorts().singleton() )
		{
			ioc->getInputComRouteData().setCast(
					ComProtocol::PROTOCOL_UNICAST_KIND );
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT SYNCHRONOUS"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT TRANSFERT
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteTransfert(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT TRANSFERT" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));
//
//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( theRoutingData.getComPoint()->is< OutputComPoint >() )
//				{
//					theExecutable->getRouter4Instance(
//						theInstanceStatic->getOffset())->setOutputRouting(
//								theComPointInstance, theRoutingData);
//					ioc->getOutputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//
//				if( theRoutingData.getComPoint()->is< InputComPoint >() )
//				{
//					theExecutable->getRouter4Instance(
//						theInstanceStatic->getOffset())->setInputRouting(
//								theComPointInstance, theRoutingData);
//					ioc->getInputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT TRANSFERT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}

/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECT ENVIRONMENT
 *******************************************************************************
 */

void CompilerOfInteraction::compileRouteEnvironment(
		ExecutableForm * theExecutable, InstanceOfConnect * ioc)
{
	const Connector * aConnector = ioc->getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECT ENVIRONMENT" << std::endl;
	aConnector->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	BFList::const_raw_iterator< ComPoint > itComPoint;
	BFList::const_raw_iterator< ComPoint > endItComPoint;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	Connector::route_iterator itComRoute = aConnector->begin();
	Connector::route_iterator endItComRoute = aConnector->end();
	for( ; itComRoute != endItComRoute ; ++itComRoute )
	{
		itComPoint = (*itComRoute)->getComPoints().begin();
		endItComPoint = (*itComRoute)->getComPoints().end();
		for( ; itComPoint != endItComPoint ; ++itComPoint )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					ioc, (*itComRoute), (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// ERROR REPORTING
				if( theRoutingData.getPort()->getModifier().isnotDirectionKind(
						(*itComRoute)->getModifier().getDirectionKind() )
					&& (not theRoutingData.getPort()->
							getModifier().isDirectionInout()) )
				{
					incrErrorCount();
					AVM_OS_WARN << (*itComRoute)->errorLocation(aConnector)
						<< "Unexpected a "
						<< theRoutingData.getPort()->getModifier().strDirection()
						<< " PORT << "
						<< theRoutingData.getPort()->getFullyQualifiedNameID()
						<< " >> in an "
						<< (*itComRoute)->getModifier().strDirection()
						<< " BUS << " << aConnector->getFullyQualifiedNameID()
						<< " >>" << std::endl;
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	ioc->toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECT ENVIRONMENT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}




/*
 *******************************************************************************
 * TOOLS FOR ROUTING DATA
 *******************************************************************************
 */
RoutingData CompilerOfInteraction::addRoutingData(
		ExecutableForm * theExecutable, bool isInstanceStaticFlag,
		InstanceOfConnect * ioc, InstanceOfMachine * theInstanceStatic,
		InstanceOfPort * thePortInstance,
		Modifier::DIRECTION_KIND aDirection)
{
	RoutingData theRoutingData(ioc, theInstanceStatic, thePortInstance);

	if( thePortInstance->isPort() )
	{
		Router & theRouter = ( isInstanceStaticFlag )
			? theExecutable->getRouter4Instance(theInstanceStatic->getOffset())
			: theExecutable->getRouter4Model(theInstanceStatic->getOffset());

		return( addRoutingData(theRouter, theRoutingData, aDirection) );
	}
	else// if( thePortInstance->isSignal() )
	{
		theRoutingData.setMID( thePortInstance->getRouteOffset() + 1 );

		return( addRoutingData(theExecutable->getRouter4This(),
				theRoutingData, aDirection) );
	}
}


RoutingData CompilerOfInteraction::addRoutingData(
		Router & theRouter, RoutingData & theRoutingData,
		Modifier::DIRECTION_KIND aDirection)
{
	switch( aDirection )
	{
		case Modifier::DIRECTION_INPUT_KIND:
		{
			theRouter.appendInputRouting(
					theRoutingData.getPort(), theRoutingData);

			theRoutingData.getConnect()->getInputComRouteData().
					appendMachinePort( theRoutingData.getMachinePort() );

			break;
		}

		case Modifier::DIRECTION_OUTPUT_KIND:
		{
			theRouter.appendOutputRouting(
					theRoutingData.getPort(), theRoutingData);

			theRoutingData.getConnect()->getOutputComRouteData().
					appendMachinePort( theRoutingData.getMachinePort() );

			break;
		}

		case Modifier::DIRECTION_INOUT_KIND:
		{
			theRouter.appendInputRouting(
					theRoutingData.getPort(), theRoutingData);

			theRoutingData.getConnect()->getInputComRouteData().
					appendMachinePort( theRoutingData.getMachinePort() );


			theRouter.appendOutputRouting(
					theRoutingData.getPort(), theRoutingData);

			theRoutingData.getConnect()->getOutputComRouteData().
					appendMachinePort( theRoutingData.getMachinePort() );

			break;
		}

		default:
		{
			theRoutingData.getConnect()->
					getAstElement()->errorLocation(AVM_OS_WARN)
					<< "Routing Data for < "
					<< str_header( theRoutingData.getPort() ) << " > !"
					<< std::endl;

			AVM_OS_EXIT( FAILED )
					<< "Unexpected Port Nature !!!"
					<< SEND_EXIT;

			break;
		}
	}

	return( theRoutingData );
}



/*
 *******************************************************************************
 * SEARCH PORT CONNECT INSTANCE
 *******************************************************************************
 */

ExecutableForm * CompilerOfInteraction::compileComPointMachine(
		ExecutableForm * theExecutable, ComPoint * aComPoint,
		bool & isInstanceStaticFlag, InstanceOfMachine * & aMachine)
{
	if( aComPoint->hasMachine() )
	{
		Machine * comMachine = aComPoint->getMachine();

		ExecutableForm * anExecutable4Port = theExecutable;
		while( anExecutable4Port != NULL )
		{
			if( anExecutable4Port->isAstElement( comMachine )
				&& anExecutable4Port->hasInstanceStaticThis() )
			{
				isInstanceStaticFlag = true;
				aMachine = anExecutable4Port->
						getInstanceStaticThis().rawMachine();

				return( anExecutable4Port );
			}
			anExecutable4Port = anExecutable4Port->getExecutableContainer();
		}

		if( comMachine->getSpecifier().hasDesignInstanceStatic() )
		{
			isInstanceStaticFlag = true;

			aMachine = theExecutable->
					getByAstInstanceStatic( comMachine ).rawMachine();
		}
		else
		{
			isInstanceStaticFlag = false;

			aMachine = theExecutable->getInstanceModel().
					getByAstElement( comMachine ).rawMachine();

			if( aMachine == NULL )
			{
				ExecutableForm * aMachineExec = getSymbolTable().
					searchExecutable(comMachine).to_ptr< ExecutableForm >();

				if( aMachineExec != NULL )
				{
					if( aMachineExec->isAncestorOf(theExecutable) )
					{
						isInstanceStaticFlag = true;
						aMachine = theExecutable->
								getInstanceStaticThis().rawMachine();
					}
					else
					{
						aMachine = new InstanceOfMachine(theExecutable,
							aMachineExec->getAstMachine(), aMachineExec,
							NULL, theExecutable->getInstanceModel().size());

						theExecutable->saveInstanceModel(aMachine);

						addMachineModelRouter(theExecutable, aMachine);
					}

					return( aMachineExec );
				}

				else
				{
					incrErrorCount();
					AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
							<< "Unfound in the COM POINT < "
							<< str_header( comMachine ) << " > !"
							<< std::endl;

					return( NULL );
				}
			}
		}

		if( aMachine != NULL )
		{
			if( aMachine->hasExecutable() )
			{
				return( aMachine->getExecutable() );
			}
			else
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint->errorLocation( aComPoint )
					<< "Unexpected in the COMP POINT < "
					<< str_header( comMachine )
					<< " > without a model with an interface !"
					<< std::endl;

				return( NULL );
			}
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
					<< "Unfound in the COM POINT < "
					<< str_header( comMachine ) << " > !"
					<< std::endl;

			return( NULL );
		}
	}

	else if( aComPoint->hasMachinePortQualifiedNameID() )
	{
		if( aComPoint->getMachinePortQualifiedNameID().is< Identifier >() )
		{
			if( theExecutable->hasInstanceStaticThis() )
			{
				isInstanceStaticFlag = true;
				aMachine = theExecutable->getInstanceStaticThis().rawMachine();

				ExecutableForm * comExec = theExecutable;
				while( comExec != NULL )
				{
					if( comExec->getPort().getByNameID( aComPoint->
							getMachinePortQualifiedNameID().str() ).valid() )
					{
						aMachine = theExecutable->
								getInstanceStaticThis().rawMachine();
						return( comExec );
					}
					comExec = comExec->getExecutableContainer();
				}
			}

			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
					<< "Unfound in the COM POINT the port contained machine < "
					<< aComPoint->getMachinePortQualifiedNameID() << " > !"
					<< std::endl;

			return( NULL );
		}


		std::string machineFQN;

		if( aComPoint->getMachinePortQualifiedNameID().
				is< QualifiedIdentifier >() )
		{
			machineFQN = aComPoint->getMachinePortQualifiedNameID().to_ptr<
					QualifiedIdentifier >()->getContainerQualifiedNameID();
		}
		else if( aComPoint->getMachinePortQualifiedNameID().
					is< UniFormIdentifier >() )
		{
			machineFQN = aComPoint->getMachinePortQualifiedNameID().
					to_ptr< UniFormIdentifier >()->toStringContainer();
		}

		if( not machineFQN.empty() )
		{
			aMachine = theExecutable->getInstanceStatic().
					getByFQNameID( machineFQN ).rawMachine();

			if( aMachine == NULL )
			{
				isInstanceStaticFlag = false;

				aMachine = theExecutable->getInstanceModel().
						getByFQNameID( machineFQN ).rawMachine();

				if( aMachine == NULL )
				{
					ExecutableForm * theMachineModel = getSymbolTable().
						searchExecutable(machineFQN).to_ptr< ExecutableForm >();

					if( theMachineModel != NULL )
					{
						aMachine = new InstanceOfMachine(theExecutable,
								theMachineModel->getAstMachine(),
								theMachineModel, NULL,
								theExecutable->getInstanceModel().size());

						theExecutable->saveInstanceModel(aMachine);

						addMachineModelRouter(theExecutable, aMachine);

						return( theMachineModel );
					}

					else
					{
						incrErrorCount();
						AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
								<< "Unfound in the COM POINT the machine < "
								<< machineFQN << " > !" << std::endl;

						return( NULL );
					}
				}
			}
		}

		if( aMachine != NULL )
		{
			if( aMachine->hasExecutable() )
			{
				return( aMachine->getExecutable() );
			}
			else
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint->errorLocation( aComPoint )
					<< "Unexpected in the COMP POINT < "
					<< aComPoint->getMachinePortQualifiedNameID().str()
					<< " > a machine without a model with an interface !"
					<< std::endl;

				return( NULL );
			}
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
					<< "Unfound in the COM POINT < "
					<< aComPoint->getMachinePortQualifiedNameID().str()
					<< " >  a machine !" << std::endl;

			return( NULL );
		}

	}

	return( (aMachine != NULL) ? aMachine->getExecutable() : NULL );
}


bool CompilerOfInteraction::compileComPointPort(
		ExecutableForm * theExecutable4Port,
		ComPoint * aComPoint, InstanceOfPort * & thePortInstance)
{
	if( aComPoint->hasPort() )
	{
		if( aComPoint->getPort()->isBasic() )
		{
			thePortInstance = getSymbolTable().searchPortConnectorInstance(
					theExecutable4Port, aComPoint->getPort());

			if( thePortInstance == NULL )
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint->errorLocation( aComPoint )
					<< "Unfound in the COM POINT the port < "
					<< aComPoint->getPort()->getFullyQualifiedNameID()
					<< " > in the model "
					<< str_header( aComPoint->getMachine() )
					<< std::endl;
			}
		}
		else //if( aComPoint->getPort()->isComposite() )
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
						<< "Unexpected the COMPOSITE PORT << "
						<< str_header( thePortInstance ) << " >> as COM POINT "
						<< std::endl << std::endl;

			return( false );
		}
	}
	else if( aComPoint->hasMachinePortQualifiedNameID() )
	{
		std::string portId;

		if( aComPoint->getMachinePortQualifiedNameID().is< Identifier >() )
		{
			portId= aComPoint->getMachinePortQualifiedNameID().str();
		}
		if( aComPoint->getMachinePortQualifiedNameID().
				is< QualifiedIdentifier >() )
		{
			portId = aComPoint->getMachinePortQualifiedNameID().
					to_ptr< QualifiedIdentifier >()->getNameID();
		}
		else if( aComPoint->getMachinePortQualifiedNameID().
				is< UniFormIdentifier >() )
		{
			portId = aComPoint->getMachinePortQualifiedNameID().
					to_ptr< UniFormIdentifier >()->toStringId();
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
					<< "Unfound in the CONNECT the port < "
					<< aComPoint->getMachinePortQualifiedNameID()
					<< " > in the model of < "
					<< str_header( theExecutable4Port ) << " > !"
					<< std::endl;

			return( false );
		}

		std::string portUfi =
			theExecutable4Port->getAstFullyQualifiedNameID() + "." + portId;

		thePortInstance = getSymbolTable().searchPortConnectorInstance(
				theExecutable4Port, portUfi);

		if( thePortInstance == NULL )
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint->errorLocation( aComPoint )
					<< "Unfound in the CONNECT the port < "
					<< portUfi << " > in the model of < "
					<< str_header( aComPoint->getMachine() ) << " > !"
					<< std::endl;

			return( false );
		}
	}

	return( thePortInstance != NULL );
}



void CompilerOfInteraction::createRoutingData(
		List< RoutingData > & listOfRoutingData,
		ExecutableForm * theExecutable, InstanceOfConnect * ioc,
		ComRoute * aComRoute, ComPoint * aComPoint)
{
	bool isInstanceStaticFlag = true;

	InstanceOfMachine * anInstanceStatic = NULL;

	ExecutableForm * anExecutable4Port = compileComPointMachine(
			theExecutable, aComPoint, isInstanceStaticFlag, anInstanceStatic);
	if( anExecutable4Port != NULL )
	{
		if( aComPoint->isMachineAllPort() )
		{
			TableOfSymbol::const_iterator itPort;
			TableOfSymbol::const_iterator endPort;

			do
			{
				itPort = anExecutable4Port->getPort().begin();
				endPort = anExecutable4Port->getPort().end();
				for( ; itPort != endPort ; ++itPort)
				{
					if( (*itPort).port().isSignal()
						|| ((*itPort).getContainer() == theExecutable) )
					{
						if( (*itPort).getModifier().hasDirectionKind(
								aComRoute->getModifier().getDirectionKind() ) )
						{
							listOfRoutingData.append( addRoutingData(
								theExecutable, isInstanceStaticFlag, ioc,
								anInstanceStatic, (*itPort).rawPort(),
								aComRoute->getModifier().getDirectionKind()) );
						}
						else
						{
							incrWarningCount();
							AVM_OS_WARN << aComPoint->warningLocation(aComPoint)
								<< "Incompatibility between the ComRoute << "
								<< aComRoute->str() << " >> & the ComPoint << "
								<< str_header( *itPort ) << " >> NATURE "
								<< std::endl << std::endl;
						}
					}
				}

				anExecutable4Port = anExecutable4Port->getExecutableContainer();
			}
			while( anExecutable4Port != NULL );
		}
		else
		{
			InstanceOfPort * aPortInstance = NULL;

			if( compileComPointPort(
					anExecutable4Port, aComPoint, aPortInstance) )
			{
				if( aPortInstance->getModifier().isDirectionKind(
						aComRoute->getModifier().getDirectionKind() )
					|| aPortInstance->getModifier().isDirectionInout() )
				{
					listOfRoutingData.append( addRoutingData(
							theExecutable, isInstanceStaticFlag,
							ioc, anInstanceStatic, aPortInstance,
							aComRoute->getModifier().getDirectionKind()) );
				}
				else
				{
					incrWarningCount();
					AVM_OS_WARN << aComPoint->warningLocation( aComPoint )
							<< "Incompatibility between the ComRoute << "
							<< aComRoute->str() << " >> & the ComPoint << "
							<< str_header( aPortInstance ) << " >> NATURE "
							<< std::endl << std::endl;
				}
			}
		}
	}
}


/**
 *******************************************************************************
 * POST-COMPILATION
 *******************************************************************************
 */

void CompilerOfInteraction::setUndefinedLocalRouteToEnv(const Router & aRouter)
{
	InstanceOfMachine * aMachine = aRouter.getMachine();

	TableOfSymbol::const_iterator itPort =
			aMachine->getExecutable()->getPort().begin();
	TableOfSymbol::const_iterator endPort =
			aMachine->getExecutable()->getPort().end();

	for( ; itPort != endPort ; ++itPort )
	{
		if( (*itPort).port().isPort() )
		{
			if( (*itPort).getModifier().hasDirectionInput()
				&& aRouter.hasntInputRouting( (*itPort).getRouteOffset() ) )
			{
				aRouter.setInputRouting((*itPort).getRouteOffset(),
						RoutingData(0, aMachine, (*itPort).rawPort(),
								ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
			}
			// NO ELSE because of INOUT PORT
			if( (*itPort).getModifier().hasDirectionOutput()
				&& aRouter.hasntOutputRouting( (*itPort).getRouteOffset() ) )
			{
				aRouter.setOutputRouting((*itPort).getRouteOffset(),
						RoutingData(0, aMachine, (*itPort).rawPort(),
								ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
			}
		}
	}
}


void CompilerOfInteraction::updateGlobalRoute(
		const Router & refRouter, const Router & newRouter)
{
	for( avm_size_t offset = 0 ; offset < mNextRouteID ; ++offset )
	{
		if( newRouter.getInputRouting(offset).invalid() )
		{
			if( refRouter.hasInputRouting(offset) )
			{
				newRouter.setInputRouting(offset,
						refRouter.getInputRouting(offset));
			}
//			else
//			{
//				newRouter.setInputRouting(offset, RoutingData(0, aMachine,
//						theMessage, ComProtocol::PROTOCOL_ENVIRONMENT_KIND)) );
//			}
		}
		// NO ELSE because of INOUT PORT
		if( newRouter.hasntOutputRouting(offset) )
		{
			if( refRouter.hasOutputRouting(offset) )
			{
				newRouter.setOutputRouting(offset,
						refRouter.getOutputRouting(offset));
			}
//			else
//			{
//				newRouter.setOutputRouting(offset, RoutingData(0, aMachine,
//						theMessage, ComProtocol::PROTOCOL_ENVIRONMENT_KIND)) );
//			}
		}
	}
}

void CompilerOfInteraction::updateLocalModelUsingLocalPrototype(
		ExecutableForm * theExecutable, const Router & aRouter4Model)
{
	InstanceOfMachine * aMachine = aRouter4Model.getMachine();

//@debug:
//	AVM_OS_TRACE << "updateLocalModelUsingLocalPrototype: "
//			<< theExecutable->getFullyQualifiedNameID() << std::endl
//			<< " >>==>> " << str_header( aMachine ) << std::endl;
//	AVM_OS_TRACE << "INIT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//	aRouter4Model.toStream(AVM_OS_TRACE);

	Router aRouter4Prototype;
	if( aMachine->getSpecifier().isDesignPrototypeStatic() )
	{
		aRouter4Prototype = theExecutable->getRouter4Prototype(aMachine);
	}

	if( aRouter4Prototype.valid() )
	{
//@debug:
//		aRouter4Prototype.toStream(AVM_OS_TRACE);
//		aRouter4Model.toStream(AVM_OS_TRACE);

		// UPDATE GLOBAL ROUTE
		updateGlobalRoute(aRouter4Prototype, aRouter4Model);

//@debug:
//		AVM_OS_TRACE << "AVANT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//		aRouter4Model.toStream(AVM_OS_TRACE);

		TableOfSymbol::const_iterator itPort =
				aMachine->getExecutable()->getPort().begin();
		TableOfSymbol::const_iterator endPort =
				aMachine->getExecutable()->getPort().end();
		for( ; itPort != endPort ; ++itPort )
		{
			if( (*itPort).getModifier().hasDirectionInput()
				&& aRouter4Model.getInputRouting(
						(*itPort).getRouteOffset()).invalid() )
			{
				if( aRouter4Prototype.getInputRouting(
						(*itPort).getRouteOffset()).valid() )
				{
					aRouter4Model.setInputRouting((*itPort).getRouteOffset(),
							aRouter4Prototype.getInputRouting(
									(*itPort).getRouteOffset()));
				}
			}
			// NO ELSE because of INOUT PORT
			if( (*itPort).getModifier().hasDirectionOutput()
				&& aRouter4Model.hasntOutputRouting(
						(*itPort).getRouteOffset()) )
			{
				if( aRouter4Prototype.getOutputRouting(
						(*itPort).getRouteOffset()).valid() )
				{
					aRouter4Model.setOutputRouting((*itPort).getRouteOffset(),
							aRouter4Prototype.getOutputRouting(
									(*itPort).getRouteOffset()));
				}
			}
		}

//@debug:
//		AVM_OS_TRACE << "APRES :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//		aRouter4Model.toStream(AVM_OS_TRACE);
//		AVM_OS_TRACE << std::endl;
	}
}


void CompilerOfInteraction::updateLocalModelUsingGlobalModel(
		const Router & aRouter4Model)
{
	InstanceOfMachine * aMachine = aRouter4Model.getMachine();

	ExecutableForm * anExecutable = aMachine->getExecutable();

//@debug:
//	AVM_OS_TRACE << "updateLocalModelUsingGlobalModel: "
//			<< theExecutable->getFullyQualifiedNameID() << std::endl
//			<< " >>==>> " << str_header( aMachine ) << std::endl;
//	AVM_OS_TRACE << "INIT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//	aRouter4Model.toStream(AVM_OS_TRACE);

	Router aRouter4ModelThis;

	if( aMachine->getSpecifier().isDesignPrototypeStatic()
		&& anExecutable->hasRouter4Instance() )
	{
		aRouter4ModelThis = anExecutable->getRouter4This();
	}
	else if( not anExecutable->hasRouter4Instance() )
	{
		anExecutable->appendRouter4Instance( aRouter4Model );

		aRouter4ModelThis = anExecutable->getRouter4This();

		if( not anExecutable->hasRouter4Model() )
		{
			anExecutable->setRouters4Model(
					anExecutable->getRouters4Instance() );
		}
	}
	else if( not anExecutable->hasRouter4Model() )
	{
		anExecutable->setRouters4Model(
				anExecutable->getRouters4Instance() );
	}


	if( aRouter4ModelThis.valid() )
	{
//@debug:
//		aRouter4ModelThis.toStream(AVM_OS_TRACE);
//		aRouter4Model.toStream(AVM_OS_TRACE);

		// UPDATE GLOBAL ROUTE
		updateGlobalRoute(aRouter4ModelThis, aRouter4Model);


//@debug:
//		AVM_OS_TRACE << "AVANT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//		aRouter4Model.toStream(AVM_OS_TRACE);

		TableOfSymbol::const_iterator itPort =
				aMachine->getExecutable()->getPort().begin();
		TableOfSymbol::const_iterator endPort =
				aMachine->getExecutable()->getPort().end();

		for( ; itPort != endPort ; ++itPort )
		{
			if( (*itPort).getModifier().hasDirectionInput()
				&& aRouter4Model.getInputRouting(
						(*itPort).getRouteOffset()).invalid() )
			{
				if( aRouter4ModelThis.getInputRouting(
						(*itPort).getRouteOffset()).valid() )
				{
					aRouter4Model.setInputRouting((*itPort).getRouteOffset(),
							aRouter4ModelThis.getInputRouting(
									(*itPort).getRouteOffset()));
				}
				else if( (*itPort).port().isPort() )
				{
					aRouter4Model.setInputRouting((*itPort).getRouteOffset(),
							RoutingData(0, aMachine, (*itPort).rawPort(),
									ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
				}
			}
			// NO ELSE because of INOUT PORT
			if( (*itPort).getModifier().hasDirectionOutput()
				&& aRouter4Model.hasntOutputRouting(
						(*itPort).getRouteOffset()) )
			{
				if( aRouter4ModelThis.getOutputRouting(
						(*itPort).getRouteOffset()).valid() )
				{
					aRouter4Model.setOutputRouting((*itPort).getRouteOffset(),
							aRouter4ModelThis.getOutputRouting(
									(*itPort).getRouteOffset()));
				}
				else if( (*itPort).port().isPort() )
				{
					aRouter4Model.setOutputRouting((*itPort).getRouteOffset(),
							RoutingData(0, aMachine, (*itPort).rawPort(),
									ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
				}
			}
		}

//@debug:
//		AVM_OS_TRACE << "APRES :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//		aRouter4Model.toStream(AVM_OS_TRACE);
//		AVM_OS_TRACE << std::endl;
	}
	else
	{
		setUndefinedLocalRouteToEnv( aRouter4Model );
	}
}


void CompilerOfInteraction::postCompileCommunication(
		ExecutableForm * theExecutable)
{
	TableOfRouter::iterator itRouter;
	TableOfRouter::iterator endRouter;

	// UPDATE DEFAULT MODEL ROUTER TO ENVIRONMENT
	if( theExecutable->hasRouter4Model() )
	{
		itRouter = theExecutable->getRouters4Model().begin();
		endRouter = theExecutable->getRouters4Model().end();
		for( ; itRouter != endRouter ; ++itRouter )
		{
			if( (*itRouter).valid() )
			{
				updateLocalModelUsingLocalPrototype(theExecutable, *itRouter);

				updateLocalModelUsingGlobalModel( *itRouter );

				updateGlobalRoute(theExecutable->getRouter4This(), *itRouter);
			}
		}

		// UPDATE DEFAULT INSTANCE ROUTER AS MODEL'S
		TableOfRoutingData::iterator itRdInst;
		TableOfRoutingData::const_iterator itRdModel;
		TableOfRoutingData::iterator endRD;

		itRouter = theExecutable->getRouters4Instance().begin();
		endRouter = theExecutable->getRouters4Instance().end();
		for( ; itRouter != endRouter ; ++itRouter )
		{
			if( (*itRouter).valid() )
			{
				const Router & theRouter = theExecutable->
						getRouter4Model((*itRouter).getMachine());

				if( theRouter == (*itRouter) )
				{
					continue;
				}
//				if( theRouter == NULL )
//				{
//					// IDENTIFICATION ROUTER(machine prototype)
//					// ==> ROUTER(machine instance)
//					theRouter = theExecutable->getRouter4Prototype(
//							(*itRouterInst)->getMachine() );
//				}

				if( theRouter != NULL )
				{
					itRdModel = theRouter.getInputRoutingTable().begin();

					itRdInst = (*itRouter).getInputRoutingTable().begin();
					endRD = (*itRouter).getInputRoutingTable().end();
					for( ; itRdInst != endRD ; ++itRdInst , ++itRdModel )
					{
						if( (*itRdInst).invalid() && (*itRdModel).valid())
						{
							(*itRdInst) = (*itRdModel);
						}
					}


					itRdModel = theRouter.getOutputRoutingTable().begin();

					itRdInst = (*itRouter).getOutputRoutingTable().begin();
					endRD = (*itRouter).getOutputRoutingTable().end();
					for( ; itRdInst != endRD ; ++itRdInst , ++itRdModel )
					{
						if( (*itRdInst).invalid() && (*itRdModel).valid())
						{
							(*itRdInst) = (*itRdModel);
						}
					}
				}
			}
		}
	}
	else
	{
		itRouter = theExecutable->getRouters4Instance().begin();
		endRouter = theExecutable->getRouters4Instance().end();
		for( ; itRouter != endRouter ; ++itRouter )
		{
			if( (*itRouter).valid() )
			{
				setUndefinedLocalRouteToEnv( (*itRouter) );
			}
		}
	}
}



}
