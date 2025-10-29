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
#include <fml/executable/InstanceOfConnector.h>
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
mNextConnectorID( 0 )
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
		ExecutableForm & aContainer, TableOfInstanceOfData & tableOfVariable,
		const Variable & aParameter, avm_offset_t offset)
{
	// #bind parameter
	if( aParameter.getModifier().hasNatureParameterBind() )
	{
		InstanceOfData * bindInstance = new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE,
				(& aContainer), aParameter, TypeManager::UNIVERSAL,
				offset, aParameter.getModifier() );
		if( aParameter.getNameID().empty() )
		{
			bindInstance->setNameID( OSS() << "$" << offset );
		}
		else
		{
			bindInstance->setNameID( aParameter.getNameID() );
		}
		bindInstance->setValue( aParameter.getValue() );

		return( BF( bindInstance ) );
	}

	// variable parameter
	else if( aParameter.getModifier().hasNatureParameter() )
	{
		TypeSpecifier aTypeSpecifier =
				compileTypeSpecifier(aContainer, aParameter.getType());

		InstanceOfData * paramInstance = new InstanceOfData(
				IPointerVariableNature::POINTER_STANDARD_NATURE,
				(& aContainer), aParameter, aTypeSpecifier, offset,
				aParameter.getModifier() );
		if( aParameter.getNameID().empty() )
		{
			paramInstance->setNameID( OSS() << "$" << offset );
		}
		else
		{
			paramInstance->setNameID( aParameter.getNameID() );
		}
		paramInstance->setValue( aParameter.getValue() );

		return( BF( paramInstance ) );
	}

	return( BF::REF_NULL );
}


void CompilerOfInteraction::precompileComPoint(ExecutableForm & aContainer,
		const PropertyPart & theDeclaration, TableOfInstanceOfData & tableOfVariable)
{
	PropertyPart::TableOfPort listOfInputPort;
	PropertyPart::TableOfPort listOfInoutPort;
	PropertyPart::TableOfPort listOfOutputPort;

	BF aParameter;
	TableOfVariable::const_ref_iterator itParam;
	TableOfVariable::const_ref_iterator endParam;

	std::size_t inoutPortCount = 0;

	// Classification of signals
	PropertyPart::TableOfSignal::const_ref_iterator its =
			theDeclaration.getSignals().begin();
	PropertyPart::TableOfSignal::const_ref_iterator endIts =
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

	aContainer.setMessageSignalCount( theDeclaration.getSignals().size() );

	// Classification of ports
	PropertyPart::TableOfPort::const_ref_iterator itp =
			theDeclaration.getPorts().begin();
	PropertyPart::TableOfPort::const_ref_iterator endItp =
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


void CompilerOfInteraction::precompileComPoint(ExecutableForm & aContainer,
		const PropertyPart::TableOfPort & listOfComPoint,
		std::size_t ioPortOffset, TableOfInstanceOfData & tableOfVariable)
{
	InstanceOfPort * newPortInstance = nullptr;

	BF aParameter;
	TableOfVariable::const_ref_iterator itParam;
	TableOfVariable::const_ref_iterator endParam;

	avm_offset_t typeOffset = 0;

	PropertyPart::TableOfPort::const_ref_iterator itPort = listOfComPoint.begin();
	PropertyPart::TableOfPort::const_ref_iterator endPort = listOfComPoint.end();
	for( avm_offset_t offset = ioPortOffset ; itPort != endPort ; ++itPort , ++offset )
	{
		newPortInstance = new InstanceOfPort((& aContainer), (itPort), offset,
				(itPort)->getParameters().size(), (itPort)->getComPointNature());

		getSymbolTable().addPortInstance(
				aContainer.savePort(newPortInstance) );

		if( newPortInstance->isSignal() )
		{
			newPortInstance->setRouteOffset( mNextRouteID++ );
		}

		itParam = (itPort)->getParameters().begin();
		endParam = (itPort)->getParameters().end();
		for( typeOffset = 0 ; itParam != endParam ; ++itParam , ++typeOffset )
		{
			aParameter = precompileParameter(aContainer,
					tableOfVariable, (itParam), typeOffset);
			newPortInstance->setParameter(typeOffset, aParameter);
		}
	}
}



void CompilerOfInteraction::precompileChannel(
		ExecutableForm & aContainer, const PropertyPart & theDeclaration,
		TableOfInstanceOfData & tableOfVariable)
{
	InstanceOfPort * newInstanceOfChannel;
	InstanceOfPort * newInstanceOfPort;

	PropertyPart::TableOfChannel::const_ref_iterator itChannel =
			theDeclaration.getChannels().begin();
	PropertyPart::TableOfChannel::const_ref_iterator endChannel =
			theDeclaration.getChannels().end();
	avm_offset_t offset = 0;
	for( ; itChannel != endChannel ; ++itChannel, ++offset )
	{
		newInstanceOfChannel = InstanceOfPort::newChannel(
				(& aContainer), (itChannel), offset);

		aContainer.saveChannel(newInstanceOfChannel);

		for( const auto & itOwned :
				(itChannel)->getParameterPart().getOwnedElements() )
		{
			// case of Signal
			if( itOwned.is< Signal >() )
			{
				const Symbol & aPort = getSymbolTable().searchPortInstance(
						itOwned.to< Port >().getSignalModel() );
				if( aPort.valid() )
				{
					newInstanceOfPort = new InstanceOfPort(
							(& aContainer), itOwned.to< Port >(),
							newInstanceOfChannel, aPort.asPort() );

					newInstanceOfChannel->appendContent(
							Symbol(newInstanceOfPort) );
				}
			}

			else if( itOwned.is< Variable >() )
			{
				//!@?UNSUPPORTED:
			}
		}
	}
}


/**
 * precompile
 * buffer
 */
void CompilerOfInteraction::precompileBuffer(
		ExecutableForm & aContainer, const Buffer & aBuffer)
{
	InstanceOfBuffer * newBufferInstance = new InstanceOfBuffer(
			aContainer, aBuffer, aContainer.getBuffer().size());

	getSymbolTable().addBufferInstance(
			aContainer.saveBuffer(newBufferInstance) );
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


void CompilerOfInteraction::compilePort(ExecutableForm & anExecutable)
{
	for( const auto & itPort : anExecutable.getPort() )
	{
		compilePort(anExecutable, itPort.asPort());
	}
}

void CompilerOfInteraction::compilePort(ExecutableForm & anExecutable,
		const InstanceOfPort & aPortInstance)
{
	for( const auto & itParam : aPortInstance.getParameters() )
	{
		if( itParam.is< InstanceOfData >() )
		{
			InstanceOfData * aVar = itParam.to_ptr< InstanceOfData >();
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

Router CompilerOfInteraction::newMachineRouter(
		const InstanceOfMachine & aMachine)
{
	Router aRouter(aMachine, mNextRouteID, mNextRouteID);

	ExecutableForm & anExecutable =
			const_cast< ExecutableForm & >( aMachine.refExecutable() );

	for( auto & itPort : anExecutable.getPort() )
	{
		if( itPort.asPort().isPort() )
		{
			// the route offset of local port w.r.t. global route offset
			itPort.setRouteOffset( mNextRouteID + itPort.getOffset() -
					anExecutable.getMessageSignalCount() );

			if( itPort.getModifier().hasDirectionInput() )
			{
				aRouter.appendInputRouting( RoutingData::nullref() );
			}
			// NO ELSE because of INOUT PORT
			if( itPort.getModifier().hasDirectionOutput() )
			{
				aRouter.appendOutputRouting( RoutingData::nullref() );
			}
		}

		else// if( itPort.isSignal() )
		{
			//!! NOTHING
		}
	}

	return( aRouter );
}


Router CompilerOfInteraction::addMachineModelRouter(
		ExecutableForm & theExecutable, const InstanceOfMachine & aMachine)
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( aMachine.getOffset() == 0 )
			<< "Unexpected the first machine model "
				"for router with offset > 0 !!!"
			<< SEND_EXIT;

	Router aRouter = newMachineRouter(aMachine);

	theExecutable.appendRouter4Model( aRouter );

	return( aRouter );
}



/**
 * compile
 * statemachine interaction
 */
void CompilerOfInteraction::compileCommunication(ExecutableForm & theExecutable,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	const Machine & aMachine = theExecutable.getAstMachine();

	if( aMachine.hasInteraction() )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable.hasInstanceStaticThis() )
				<< "Unexpected communicated Machine without submachine THIS !!!"
				<< SEND_EXIT;

		std::size_t nbComMachineCount = 0;

		TableOfRouter & theTableOfRouter4Instance =
				theExecutable.getRouters4Instance();

		// Attention: the offset of routing table of an instance machine is
		// the same than the offset of this instance
		for( const auto & itMachine : theExecutable.getInstanceStatic() )
		{
			if( itMachine.getExecutable().hasPort() )
			{
				++nbComMachineCount;
				theTableOfRouter4Instance.append(
						newMachineRouter(itMachine.machine()) );
//!@?DEBUG:
//AVM_OS_TRACE << "compileCommunication :> INIT " << str_header( theExecutable ) << std::endl;
//theTableOfRouter4Instance->last()->toStream(AVM_OS_TRACE);
			}
			else if( itMachine.getAstMachine().hasInteraction() )
			{
				++nbComMachineCount;
				theTableOfRouter4Instance.append(
						newMachineRouter(itMachine.machine()) );
//!@?DEBUG:
//AVM_OS_TRACE << "compileCommunication :> INIT " << str_header( theExecutable ) << std::endl;
//theTableOfRouter4Instance->last()->toStream(AVM_OS_TRACE);
			}
			else
			{
				theTableOfRouter4Instance.append( Router::nullref() );
			}
		}

		// For MACHINE MODEL
		TableOfRouter & theTableOfRouter4Model =
				theExecutable.getRouters4Model();

		// Router for instance machine THIS
		theTableOfRouter4Model.append( theExecutable.getRouter4This() );

		TableOfSymbol::const_iterator itMachine =
				theExecutable.instance_model_begin();
		TableOfSymbol::const_iterator endMachine =
				theExecutable.instance_model_end();
		for( ; itMachine != endMachine ; ++itMachine )
		{
			if( (*itMachine).getExecutable().hasPort() )
			{
				++nbComMachineCount;
				theTableOfRouter4Model.append(
						newMachineRouter((*itMachine).machine()) );
//!@?DEBUG:
//AVM_OS_TRACE << "compileCommunication :> INIT " << str_header( theExecutable ) << std::endl;
//theTableOfRouter4Model->last()->toStream(AVM_OS_TRACE);
			}
			else if( (*itMachine).getAstMachine().hasInteraction() )
			{
				++nbComMachineCount;
				theTableOfRouter4Model.append(
						newMachineRouter((*itMachine).machine()) );
//!@?DEBUG:
//AVM_OS_TRACE << "compileCommunication :> INIT " << str_header( theExecutable ) << std::endl;
//theTableOfRouter4Model->last()->toStream(AVM_OS_TRACE);
			}
			else
			{
				theTableOfRouter4Model.append( Router::nullref() );
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
			theExecutable.getRouters4Instance().clear();

			theExecutable.getRouters4Model().clear();
		}
	}

	else if( aMachine.hasPortSignal()
			&& ( aMachine.getSpecifier().isComponentSystem()
				|| (not aMachine.getContainerMachine()->hasInteraction()) ) )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( theExecutable.hasInstanceStaticThis() )
				<< "Unexpected communicated Machine without submachine THIS !!!"
				<< SEND_EXIT;

		Router bfRouter = newMachineRouter(
				theExecutable.getInstanceStaticThis().machine());

		theExecutable.appendRouter4Instance( bfRouter );

		if( not aMachine.getSpecifier().isComponentSystem() )
		{
			theExecutable.appendRouter4Model( bfRouter );
		}

//!@?DEBUG:
//AVM_OS_TRACE << "compileCommunication :> INIT " << str_header( aMachine ) << std::endl;
//theRouterTable->last()->toStream(AVM_OS_TRACE);

		postCompileCommunication(theExecutable);
	}
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnector(ExecutableForm & theExecutable,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	const Machine & aMachine = theExecutable.getAstMachine();

	InstanceOfConnector * newConnector = nullptr;

	const InteractionPart * theInteractionPart = aMachine.getInteraction();
	if( theInteractionPart != nullptr )
	{
		for( const auto & itConnector : theInteractionPart->getConnectors() )
		{
			newConnector = new InstanceOfConnector( (& theExecutable),
					itConnector, theExecutable.getConnector().size(),
					itConnector.getProtocol(), itConnector.getCast() );

			getSymbolTable().addConnectorInstance(
					theExecutable.saveConnector(newConnector) );

			////////////////////////////////////////////////////////////////////
			// For PORT
			if( itConnector.isPort() )
			{
				compileConnector(theExecutable, itConnector, *newConnector,
						hasSynchronizeMachine, hasUpdateBuffer);
			}

			////////////////////////////////////////////////////////////////////
			// For MESSAGE OR SIGNAL
			else if( itConnector.isSignal() )
			{
				compileRoute(theExecutable, itConnector, *newConnector,
						hasSynchronizeMachine, hasUpdateBuffer);
			}
		}
	}
}



void CompilerOfInteraction::compileConnector(ExecutableForm & theExecutable,
		const Connector & astConnector, InstanceOfConnector & aConnector,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	// One unique Connector ID per connector!
	aConnector.setMID( ++mNextConnectorID );
	switch( astConnector.getProtocol() )
	{
		case ComProtocol::PROTOCOL_BUFFER_KIND:
		{
			compileConnectorBuffer(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_RDV_KIND:
		case ComProtocol::PROTOCOL_MULTIRDV_KIND:
		{
			hasSynchronizeMachine = true;
			compileConnectorSynchronous(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_FLOW_KIND:
		{
			hasSynchronizeMachine = true;
			compileConnectorFlow(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:
		{
			hasUpdateBuffer = true;
			compileConnectorBroadcast(theExecutable, aConnector);
			break;
		}


		case ComProtocol::PROTOCOL_TRANSFERT_KIND:
		{
			compileConnectorTransfert(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
		{
			compileConnectorEnvironment(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		case ComProtocol::PROTOCOL_ANYCAST_KIND:
		{
			compileConnectorRoutingCast(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			// ERROR REPORTING
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unexpected for the connector<port> the protocol << "
					<< astConnector.strProtocolCast(true) << " >>"
					<< std::endl;

			break;
		}
	}
}

void CompilerOfInteraction::compileRoute(ExecutableForm & theExecutable,
		const Connector & astConnector, InstanceOfConnector & aConnector,
		bool & hasSynchronizeMachine, bool & hasUpdateBuffer)
{
	switch( astConnector.getProtocol() )
	{
		case ComProtocol::PROTOCOL_BUFFER_KIND:
		{
			compileRouteBuffer(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_RDV_KIND:
		case ComProtocol::PROTOCOL_MULTIRDV_KIND:
		{
			hasSynchronizeMachine = true;
			compileRouteSynchronous(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_BROADCAST_KIND:
		{
			hasUpdateBuffer = true;
			compileRouteBroadcast(theExecutable, aConnector);
			break;
		}


		case ComProtocol::PROTOCOL_TRANSFERT_KIND:
		{
			compileRouteTransfert(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_ENVIRONMENT_KIND:
		{
			compileRouteEnvironment(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_MULTICAST_KIND:
		case ComProtocol::PROTOCOL_UNICAST_KIND:
		case ComProtocol::PROTOCOL_ANYCAST_KIND:
		{
			compileRouteRoutingCast(theExecutable, aConnector);
			break;
		}

		case ComProtocol::PROTOCOL_UNDEFINED_KIND:
		default:
		{
			// ERROR REPORTING
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unexpected for the connector<message|signal> "
							"the protocol << "
					<< astConnector.strProtocolCast(true) << " >>"
					<< std::endl;

			break;
		}
	}
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR BROADCAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorBroadcast(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR BROADCAST" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	InstanceOfBuffer * theBufferInstance = nullptr;

	if( astConnector.hasBuffer() )
	{
		const Buffer & buffer = astConnector.getBuffer();

		if( buffer.isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(
					theExecutable, buffer, theExecutable.getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable.saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					(& theExecutable), buffer).rawBuffer();
		}
	}
	else if( astConnector.hasBufferUfid() )
	{
		theBufferInstance = getSymbolTable().searchBufferInstance(
				theExecutable, astConnector.strBufferUfid()).rawBuffer();

		if( theBufferInstance == nullptr )
		{
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unfound in the CONNECTOR the buffer instance < "
					<< astConnector.strBufferUfid() << " > !" << std::endl;
		}
	}
	else //if( buffer == nullptr )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable, Buffer::nullref(),
				theExecutable.getBuffer().size(), TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable.saveBuffer(theBufferInstance) );
	}

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// for buffer port
				if( theBufferInstance != nullptr )
				{
					theRoutingData.appendBuffer(theBufferInstance);
				}

				if( itComRoute.hasProtocol() )
				{
					// TODO for other COM_PROTOCOL
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR BROADCAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR BUFFER
 *******************************************************************************
 */

static void bufferCompletion(
		List< RoutingData > & listOfOutRoutingData,
		List< RoutingData > & listOfInRoutingData)
{
	List< RoutingData >::iterator inRD;
	List< RoutingData >::iterator outRD;

	bool hasnoBuffer;

	inRD = listOfInRoutingData.begin();
	for( ; inRD != listOfInRoutingData.end() ; ++inRD )
	{
		hasnoBuffer = inRD->getBufferInstance().empty();

		if( listOfOutRoutingData.nonempty() )
		{
			outRD = listOfOutRoutingData.begin();
			for( ; outRD != listOfOutRoutingData.end() ; ++outRD )
			{
				if( hasnoBuffer && outRD->getBufferInstance().nonempty() )
				{
					inRD->getBufferInstance().append(
							outRD->getBufferInstance() );
				}
			}

			inRD->getBufferInstance().makeUnique();
		}
	}

	outRD = listOfOutRoutingData.begin();
	for( ; outRD != listOfOutRoutingData.end() ; ++outRD )
	{
		hasnoBuffer = (outRD)->getBufferInstance().empty();

		if( listOfInRoutingData.nonempty() )
		{
			inRD = listOfInRoutingData.begin();
			for( ; inRD != listOfInRoutingData.end() ; ++inRD )
			{
				if( hasnoBuffer && (inRD)->getBufferInstance().nonempty() )
				{
					(outRD)->getBufferInstance().append(
							(inRD)->getBufferInstance() );
				}
			}

			(outRD)->getBufferInstance().makeUnique();
		}
	}
}


void CompilerOfInteraction::compileConnectorBuffer(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR BUFFER" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	InstanceOfBuffer * theBufferInstance = nullptr;
	InstanceOfBuffer * localBufferInstance = nullptr;

	if( astConnector.hasBuffer() )
	{
		const Buffer & buffer = astConnector.getBuffer();

		if( buffer.isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(theExecutable,
					buffer, theExecutable.getBuffer().size() );

			getSymbolTable().addBufferInstance(
					theExecutable.saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					(& theExecutable), buffer).rawBuffer();
		}
	}
	else if( astConnector.hasBufferUfid() )
	{
		theBufferInstance = getSymbolTable().searchBufferInstance(
				theExecutable, astConnector.strBufferUfid()).rawBuffer();

		if( theBufferInstance == nullptr )
		{
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unfound in the CONNECTOR the buffer instance < "
					<< astConnector.strBufferUfid() << " > !" << std::endl;
		}
	}
	else //if( buffer == nullptr )
	{
		theBufferInstance = new InstanceOfBuffer(
				theExecutable,	Buffer::nullref(),
				theExecutable.getBuffer().size(), TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable.saveBuffer(theBufferInstance) );
	}

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				if( theBufferInstance != nullptr )
				{
					// for buffer port
					theRoutingData.appendBuffer(theBufferInstance);
				}

				switch( itComRoute.getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						localBufferInstance = theBufferInstance;

						if( itComRoute.hasBuffer() )
						{
							const Buffer & buffer = itComRoute.getBuffer();
							if( buffer.isAnonymID() )
							{
								localBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable.getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable.saveBuffer(
											localBufferInstance) );
							}
							else
							{
								localBufferInstance = getSymbolTable().
									searchBufferInstance(
										(& theExecutable), buffer).rawBuffer();
							}
						}
						else if( itComRoute.hasBufferUfid() )
						{
							localBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									itComRoute.strBufferUfid()).rawBuffer();

							if( localBufferInstance == nullptr )
							{
								incrErrorCount();
								astConnector.errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< astConnector.strBufferUfid()
										<< " > !"
										<< std::endl;
							}
						}

						if( localBufferInstance != nullptr )
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
				if( itComRoute.getModifier().isDirectionOutput() )
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
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR BUFFER"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR ROUTING CAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorRoutingCast(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR ROUTING CAST" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	InstanceOfBuffer * theBufferInstance = nullptr;

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// list for update input buffer and port connector list
				listOfOutRoutingData.append(theRoutingData);

				switch( itComRoute.getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						if( itComRoute.hasBuffer() )
						{
							const Buffer & buffer = itComRoute.getBuffer();

							if( buffer.isAnonymID() )
							{
								theBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable.getBuffer().size());

								getSymbolTable().addBufferInstance(
										theExecutable.saveBuffer(
												theBufferInstance) );
							}
							else
							{
								theBufferInstance = getSymbolTable().
									searchBufferInstance(
										(& theExecutable), buffer).rawBuffer();
							}
						}
						else if( itComRoute.hasBufferUfid() )
						{
							theBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									itComRoute.strBufferUfid()).rawBuffer();

							if( theBufferInstance == nullptr )
							{
								incrErrorCount();
								astConnector.errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< itComRoute.strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( theBufferInstance != nullptr )
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
				if( itComRoute.getModifier().isDirectionOutput() )
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
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR ROUTING CAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR SYNCHRONOUS
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorSynchronous(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR SYNCHRONOUS"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		if( itComRoute.hasCast() )
		{
			if( itComRoute.getModifier().isDirectionOutput() )
			{
				aConnector.setOutputProtocolCast( itComRoute.getCast() );
			}
			else
			{
				aConnector.setInputProtocolCast( itComRoute.getCast() );
			}
		}

		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			if( itComRoute.hasProtocol() )
			{
				// TODO for other COM_PROTOCOL
			}
		}
	}

	if( aConnector.getProtocol() == ComProtocol::PROTOCOL_MULTIRDV_KIND )
	{
		if( (not aConnector.hasOutputProtocolCast())
			&& aConnector.singletonOutputMachinePort() )
		{
			aConnector.setOutputProtocolCast( ComProtocol::PROTOCOL_UNICAST_KIND );
		}

		if( (not aConnector.hasInputProtocolCast())
			&& aConnector.singletonInputMachinePort() )
		{
			aConnector.setInputProtocolCast( ComProtocol::PROTOCOL_UNICAST_KIND );
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR SYNCHRONOUS"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR FLOW
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorFlow(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR FLOW"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			if( itComRoute.hasProtocol() )
			{
				// TODO for other COM_PROTOCOL
			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR FLOW"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR TRANSFERT
 *******************************************************************************
 */
void CompilerOfInteraction::compileConnectorTransfert(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR TRANSFERT"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( theRoutingData.getComPoint()->is< OutputComPoint >() )
//				{
//					theExecutable.getRouter4Instance(
//						theInstanceStatic->getOffset())->setOutputRouting(
//								theComPointInstance, theRoutingData);
//					aConnector.getOutputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//
//				if( theRoutingData.getComPoint()->is< InputComPoint >() )
//				{
//					theExecutable.getRouter4Instance(
//						theInstanceStatic->getOffset())->setInputRouting(
//								theComPointInstance, theRoutingData);
//					aConnector.getInputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR TRANSFERT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}

/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR ENVIRONMENT
 *******************************************************************************
 */

void CompilerOfInteraction::compileConnectorEnvironment(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR ENVIRONMENT"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// ERROR REPORTING
				if( theRoutingData.getPort().getModifier().isnotDirectionKind(
						itComRoute.getModifier().getDirectionKind() )
					&& (not theRoutingData.getPort().
							getModifier().isDirectionInout()) )
				{
					incrErrorCount();
					AVM_OS_WARN << itComRoute.errorLocation(astConnector)
						<< "Unexpected a "
						<< theRoutingData.getPort().getModifier().strDirection()
						<< " PORT << "
						<< theRoutingData.getPort().getFullyQualifiedNameID()
						<< " >> in an "
						<< itComRoute.getModifier().strDirection()
						<< " CONNECTOR << "
						<< astConnector.getFullyQualifiedNameID()
						<< " >>" << std::endl;
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR ENVIRONMENT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}








/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR BROADCAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteBroadcast(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR BROADCAST"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	const Buffer * buffer = nullptr;
	InstanceOfBuffer * theBufferInstance = nullptr;

	if( astConnector.hasBuffer() )
	{
		buffer = &( astConnector.getBuffer() );

		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(theExecutable,
					(* buffer), theExecutable.getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable.saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					(& theExecutable), (*buffer)).rawBuffer();
		}
	}
	else if( astConnector.hasBufferUfid() )
	{
		theBufferInstance = getSymbolTable().searchBufferInstance(
				theExecutable, astConnector.strBufferUfid()).rawBuffer();

		if( theBufferInstance == nullptr )
		{
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unfound in the CONNECTOR the buffer instance < "
					<< astConnector.strBufferUfid() << " > !" << std::endl;
		}
	}
	else if( buffer == nullptr )
	{
		theBufferInstance = new InstanceOfBuffer( theExecutable, (* buffer),
				theExecutable.getBuffer().size(), TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable.saveBuffer(theBufferInstance) );
	}

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// for buffer port
				if( theBufferInstance != nullptr )
				{
					theRoutingData.appendBuffer(theBufferInstance);
				}

				if( itComRoute.hasProtocol() )
				{
					// TODO for other COM_PROTOCOL
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR BROADCAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR BUFFER
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteBuffer(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR BUFFER" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	const Buffer * buffer = nullptr;
	InstanceOfBuffer * theBufferInstance = nullptr;
	InstanceOfBuffer * localBufferInstance = nullptr;

	if( astConnector.hasBuffer() )
	{
		buffer = &( astConnector.getBuffer() );
		if( buffer->isAnonymID() )
		{
			theBufferInstance = new InstanceOfBuffer(theExecutable,
					(* buffer), theExecutable.getBuffer().size());

			getSymbolTable().addBufferInstance(
					theExecutable.saveBuffer(theBufferInstance) );
		}
		else
		{
			theBufferInstance = getSymbolTable().searchBufferInstance(
					(& theExecutable), (* buffer)).rawBuffer();
		}
	}
	else if( astConnector.hasBufferUfid() )
	{
		theBufferInstance = getSymbolTable().searchBufferInstance(
				theExecutable, astConnector.strBufferUfid()).rawBuffer();

		if( theBufferInstance == nullptr )
		{
			incrErrorCount();
			astConnector.errorLocation(AVM_OS_WARN)
					<< "Unfound in the ROUTE the buffer instance < "
					<< astConnector.strBufferUfid() << " > !" << std::endl;
		}
	}
	else if( buffer == nullptr )
	{
		theBufferInstance = new InstanceOfBuffer( theExecutable, (* buffer),
				theExecutable.getBuffer().size(), TYPE_FIFO_SPECIFIER, -1 );

		getSymbolTable().addBufferInstance(
				theExecutable.saveBuffer(theBufferInstance) );
	}

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				if( theBufferInstance != nullptr )
				{
					// for buffer port
					theRoutingData.appendBuffer(theBufferInstance);
				}

				// for buffer port
				if( not itComRoute.hasProtocol() )
				{
					continue;
				}

				switch( itComRoute.getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						localBufferInstance = theBufferInstance;

						if( itComRoute.hasBuffer() )
						{
							const Buffer & buffer = itComRoute.getBuffer();

							if( buffer.isAnonymID() )
							{
								localBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable.getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable.saveBuffer(
											localBufferInstance) );
							}
							else
							{
								localBufferInstance = getSymbolTable().
									searchBufferInstance((& theExecutable),
											buffer).rawBuffer();
							}
						}
						else if( itComRoute.hasBufferUfid() )
						{
							localBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									itComRoute.strBufferUfid()).rawBuffer();

							if( localBufferInstance == nullptr )
							{
								incrErrorCount();
								astConnector.errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< itComRoute.strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( localBufferInstance != nullptr )
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
				if( itComRoute.getModifier().isDirectionOutput() )
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
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR BUFFER"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR ROUTING CAST
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteRoutingCast(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR ROUTING CAST"
			<< std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	InstanceOfBuffer * theBufferInstance = nullptr;

	// lists for update input port connector list
	List< RoutingData > listOfOutRoutingData;
	List< RoutingData > listOfInRoutingData;

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		if( itComRoute.getModifier().isDirectionOutput() )
		{
			aConnector.setOutputProtocolCast( itComRoute.getCast() );
		}
		else
		{
			aConnector.setInputProtocolCast( itComRoute.getCast() );
		}

		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// list for update input buffer and port connector list
				listOfOutRoutingData.append(theRoutingData);

				switch( itComRoute.getProtocol() )
				{
					case ComProtocol::PROTOCOL_BUFFER_KIND:
					{
						if( itComRoute.hasBuffer() )
						{
							const Buffer & buffer = itComRoute.getBuffer();

							if( buffer.isAnonymID() )
							{
								theBufferInstance = new InstanceOfBuffer(
										theExecutable, buffer,
										theExecutable.getBuffer().size());

								getSymbolTable().addBufferInstance(
									theExecutable.saveBuffer(theBufferInstance));
							}
							else
							{
								theBufferInstance = getSymbolTable().
									searchBufferInstance((& theExecutable),
											buffer).rawBuffer();
							}
						}
						else if( itComRoute.hasBufferUfid() )
						{
							theBufferInstance = getSymbolTable().
								searchBufferInstance(theExecutable,
									itComRoute.strBufferUfid()).rawBuffer();

							if( theBufferInstance == nullptr )
							{
								incrErrorCount();
								astConnector.errorLocation(AVM_OS_WARN)
										<< "Unfound in the COM POINT "
												"the buffer instance < "
										<< itComRoute.strBufferUfid()
										<< " > !" << std::endl;
							}
						}

						if( theBufferInstance != nullptr )
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
					case ComProtocol::PROTOCOL_UNICAST_KIND:
					case ComProtocol::PROTOCOL_ANYCAST_KIND:
					{
						break;
					}

					case ComProtocol::PROTOCOL_UNDEFINED_KIND:
					{
						break;
					}

					default:
					{
						incrErrorCount();
						astConnector.errorLocation(AVM_OS_WARN)
								<< "Unexpected protocol < "
								<< ComProtocol::strProtocol(
										itComRoute.getProtocol() )
								<< " > in CAST routing in the "
									"COM ROUTE the buffer instance < "
								<< itComRoute.str() << " > !" << std::endl;
						break;
					}
				}

				// list for update all buffer and port connector list
				if( itComRoute.getModifier().isDirectionOutput() )
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
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR ROUTING CAST"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}


/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR SYNCHRONOUS
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteSynchronous(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR SYNCHRONOUS" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		if( itComRoute.hasCast() )
		{
			if( itComRoute.getModifier().isDirectionOutput() )
			{
				aConnector.setOutputProtocolCast( itComRoute.getCast() );
			}
			else
			{
				aConnector.setInputProtocolCast( itComRoute.getCast() );
			}
		}

		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( itComRoute.hasProtocol() )
//				{
//					// TODO for other COM_PROTOCOL
//				}
//			}
		}
	}

	if( aConnector.getProtocol() == ComProtocol::PROTOCOL_MULTIRDV_KIND )
	{
		if( (not aConnector.hasOutputProtocolCast())
			&& aConnector.singletonOutputMachinePort() )
		{
			aConnector.setOutputProtocolCast( ComProtocol::PROTOCOL_UNICAST_KIND );
		}

		if( (not aConnector.hasInputProtocolCast())
			&& aConnector.singletonInputMachinePort() )
		{
			aConnector.setInputProtocolCast( ComProtocol::PROTOCOL_UNICAST_KIND );
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR SYNCHRONOUS"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}



/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR TRANSFERT
 *******************************************************************************
 */
void CompilerOfInteraction::compileRouteTransfert(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR TRANSFERT" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;
//	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));
//
//			while( listOfRoutingData.nonempty() )
//			{
//				listOfRoutingData.pop_first_to( theRoutingData );
//
//				if( theRoutingData.getComPoint()->is< OutputComPoint >() )
//				{
//					theExecutable.getRouter4Instance(
//						theInstanceStatic->getOffset())->setOutputRouting(
//								theComPointInstance, theRoutingData);
//					aConnector.getOutputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//
//				if( theRoutingData.getComPoint()->is< InputComPoint >() )
//				{
//					theExecutable.getRouter4Instance(
//						theInstanceStatic->getOffset())->setInputRouting(
//								theComPointInstance, theRoutingData);
//					aConnector.getInputComRouteData().appendMachineComPoint(
//							theRoutingData.getMachinePort() );
//				}
//			}
		}
	}


AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR TRANSFERT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}

/*
 *******************************************************************************
 * COMPILE INTERACTION CONNECTOR ENVIRONMENT
 *******************************************************************************
 */

void CompilerOfInteraction::compileRouteEnvironment(
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector)
{
	const Connector & astConnector = aConnector.getAstConnector();

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	AVM_OS_TRACE << INCR_INDENT_TAB
			<< "COMPILE INTERACTION CONNECTOR ENVIRONMENT" << std::endl;
	astConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )

	List< RoutingData > listOfRoutingData;
	RoutingData theRoutingData;

	// Routing for all port
	for( const auto & itComRoute : astConnector.getComRoutes() )
	{
		for( const auto & itComPoint : itComRoute.getComPoints() )
		{
			createRoutingData(listOfRoutingData, theExecutable,
					aConnector, itComRoute, (itComPoint));

			while( listOfRoutingData.nonempty() )
			{
				listOfRoutingData.pop_first_to( theRoutingData );

				// ERROR REPORTING
				if( theRoutingData.getPort().getModifier().isnotDirectionKind(
						itComRoute.getModifier().getDirectionKind() )
					&& (not theRoutingData.getPort().
							getModifier().isDirectionInout()) )
				{
					incrErrorCount();
					AVM_OS_WARN << itComRoute.errorLocation(astConnector)
						<< "Unexpected a "
						<< theRoutingData.getPort().getModifier().strDirection()
						<< " PORT << "
						<< theRoutingData.getPort().getFullyQualifiedNameID()
						<< " >> in an "
						<< itComRoute.getModifier().strDirection()
						<< " CONNECTOR << "
						<< astConnector.getFullyQualifiedNameID()
						<< " >>" << std::endl;
				}
			}
		}
	}

AVM_IF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
	aConnector.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB_DECR_INDENT
			<< "END COMPILE INTERACTION CONNECTOR ENVIRONMENT"
			<< std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( COMPILING , COMMUNICATION )
}




/*
 *******************************************************************************
 * TOOLS FOR ROUTING DATA
 *******************************************************************************
 */
RoutingData CompilerOfInteraction::addRoutingData(
		ExecutableForm & theExecutable, bool isInstanceStaticFlag,
		InstanceOfConnector & aConnector,
		const InstanceOfMachine & theInstanceStatic,
		const InstanceOfPort & thePortInstance, const ComRoute & aComRoute)
{
	RoutingData theRoutingData(aConnector, theInstanceStatic, thePortInstance);

	if( thePortInstance.isPort() )
	{
		Router & theRouter = ( isInstanceStaticFlag )
			? theExecutable.getRouter4Instance(theInstanceStatic.getOffset())
			: theExecutable.getRouter4Model(theInstanceStatic.getOffset());

		return( addRoutingData(aConnector,
				theRouter, theRoutingData, aComRoute) );
	}
	else// if( thePortInstance.isSignal() )
	{
		theRoutingData.setMID( thePortInstance.getRouteOffset() + 1 );

		return( addRoutingData(aConnector,
				theExecutable.getRouter4This(), theRoutingData, aComRoute ) );
	}
}


RoutingData CompilerOfInteraction::addRoutingData(
		InstanceOfConnector & aConnector, Router & theRouter,
		RoutingData & theRoutingData, const ComRoute & aComRoute)
{
	switch( aComRoute.getModifier().getDirectionKind() )
	{
		case Modifier::DIRECTION_INPUT_KIND:
		{
			theRouter.appendInputRouting(
					theRoutingData.getPort(), theRoutingData);

			aConnector.appendInputRoutingData( theRoutingData );

			break;
		}

		case Modifier::DIRECTION_OUTPUT_KIND:
		{
			theRouter.appendOutputRouting(
					theRoutingData.getPort(), theRoutingData);

			aConnector.appendOutputRoutingData( theRoutingData );

			break;
		}

		case Modifier::DIRECTION_INOUT_KIND:
		{
			theRouter.appendInputRouting(
					theRoutingData.getPort(), theRoutingData);

			aConnector.appendInputRoutingData( theRoutingData );


			theRouter.appendOutputRouting(
					theRoutingData.getPort(), theRoutingData);

			aConnector.appendOutputRoutingData( theRoutingData );

			break;
		}

		default:
		{
			theRoutingData.getConnector().
					safeAstElement().errorLocation(AVM_OS_WARN)
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
 * SEARCH PORT CONNECTOR INSTANCE
 *******************************************************************************
 */

ExecutableForm * CompilerOfInteraction::compileComPointMachine(
		ExecutableForm & theExecutable, const ComPoint & aComPoint,
		bool & isInstanceStaticFlag, InstanceOfMachine * & aMachine)
{
	if( aComPoint.hasMachine() )
	{
		const Machine & comMachine = aComPoint.getMachine();

		ExecutableForm * anExecutable4Port = (& theExecutable);
		while( anExecutable4Port != nullptr )
		{
			if( anExecutable4Port->isAstElement(comMachine)
				&& anExecutable4Port->hasInstanceStaticThis() )
			{
				isInstanceStaticFlag = true;
				aMachine = anExecutable4Port->
						getInstanceStaticThis().rawMachine();

				return( anExecutable4Port );
			}
			anExecutable4Port = anExecutable4Port->getExecutableContainer();
		}

		if( comMachine.getSpecifier().hasDesignInstanceStatic() )
		{
			isInstanceStaticFlag = true;

			aMachine = theExecutable.
					getByAstInstanceStatic(comMachine).rawMachine();
		}
		else
		{
			isInstanceStaticFlag = false;

			aMachine = theExecutable.getInstanceModel().
					getByAstElement(comMachine).rawMachine();

			if( aMachine == nullptr )
			{
				ExecutableForm * aMachineExec = getSymbolTable().
					searchExecutable(comMachine).to_ptr< ExecutableForm >();

				if( aMachineExec != nullptr )
				{
					if( aMachineExec->isAncestorOf(& theExecutable) )
					{
						isInstanceStaticFlag = true;
						aMachine = theExecutable.
								getInstanceStaticThis().rawMachine();
					}
					else
					{
						aMachine = new InstanceOfMachine((& theExecutable),
							aMachineExec->getAstMachine(), (* aMachineExec),
							nullptr, theExecutable.getInstanceModel().size());

						theExecutable.saveInstanceModel(aMachine);

						addMachineModelRouter(theExecutable, (* aMachine));
					}

					return( aMachineExec );
				}

				else
				{
					incrErrorCount();
					AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
							<< "Unfound in the COM POINT < "
							<< str_header( comMachine ) << " > !"
							<< std::endl;

					return( nullptr );
				}
			}
		}

		if( aMachine != nullptr )
		{
			if( aMachine->hasExecutable() )
			{
				return( aMachine->getExecutable() );
			}
			else
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint.errorLocation( aComPoint )
					<< "Unexpected in the COMP POINT < "
					<< str_header( comMachine )
					<< " > without a model with an interface !"
					<< std::endl;

				return( nullptr );
			}
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
					<< "Unfound in the COM POINT < "
					<< str_header( comMachine ) << " > !"
					<< std::endl;

			return( nullptr );
		}
	}

	else if( aComPoint.hasMachinePortQualifiedNameID() )
	{
		if( aComPoint.getMachinePortQualifiedNameID().is< Identifier >() )
		{
			if( theExecutable.hasInstanceStaticThis() )
			{
				isInstanceStaticFlag = true;
				aMachine = theExecutable.getInstanceStaticThis().rawMachine();

				ExecutableForm * comExec = (& theExecutable);
				while( comExec != nullptr )
				{
					if( comExec->getPort().getByNameID( aComPoint.
							getMachinePortQualifiedNameID().str() ).valid() )
					{
						aMachine = theExecutable.
								getInstanceStaticThis().rawMachine();
						return( comExec );
					}
					comExec = comExec->getExecutableContainer();
				}
			}

			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
					<< "Unfound in the COM POINT the port contained machine < "
					<< aComPoint.getMachinePortQualifiedNameID() << " > !"
					<< std::endl;

			return( nullptr );
		}


		std::string machineFQN;

		if( aComPoint.getMachinePortQualifiedNameID().
				is< QualifiedIdentifier >() )
		{
			machineFQN = aComPoint.getMachinePortQualifiedNameID().to<
					QualifiedIdentifier >().getContainerQualifiedNameID();
		}
		else if( aComPoint.getMachinePortQualifiedNameID().
					is< UniFormIdentifier >() )
		{
			machineFQN = aComPoint.getMachinePortQualifiedNameID().
					to< UniFormIdentifier >().toStringContainer();
		}

		if( not machineFQN.empty() )
		{
			aMachine = theExecutable.getInstanceStatic().
					getByFQNameID( machineFQN ).rawMachine();

			if( aMachine == nullptr )
			{
				isInstanceStaticFlag = false;

				aMachine = theExecutable.getInstanceModel().
						getByFQNameID( machineFQN ).rawMachine();

				if( aMachine == nullptr )
				{
					ExecutableForm * theMachineModel = getSymbolTable().
						searchExecutable(machineFQN).to_ptr< ExecutableForm >();

					if( theMachineModel != nullptr )
					{
						aMachine = new InstanceOfMachine((& theExecutable),
								theMachineModel->getAstMachine(),
								(* theMachineModel), nullptr,
								theExecutable.getInstanceModel().size());

						theExecutable.saveInstanceModel(aMachine);

						addMachineModelRouter(theExecutable, (* aMachine));

						return( theMachineModel );
					}

					else
					{
						incrErrorCount();
						AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
								<< "Unfound in the COM POINT the machine < "
								<< machineFQN << " > !" << std::endl;

						return( nullptr );
					}
				}
			}
		}

		if( aMachine->isnotNullref() )
		{
			if( aMachine->hasExecutable() )
			{
				return( aMachine->getExecutable() );
			}
			else
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint.errorLocation( aComPoint )
					<< "Unexpected in the COMP POINT < "
					<< aComPoint.getMachinePortQualifiedNameID().str()
					<< " > a machine without a model with an interface !"
					<< std::endl;

				return( nullptr );
			}
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
					<< "Unfound in the COM POINT < "
					<< aComPoint.getMachinePortQualifiedNameID().str()
					<< " >  a machine !" << std::endl;

			return( nullptr );
		}

	}

	return( aMachine->isnotNullref() ? aMachine->getExecutable() : nullptr );
}


bool CompilerOfInteraction::compileComPointPort(
		ExecutableForm & theExecutableOfConnector,
		ExecutableForm & theExecutable4Port,
		const ComPoint & aComPoint, InstanceOfPort * & thePortInstance)
{
	if( aComPoint.hasPort() )
	{
		if( aComPoint.getPort().isBasic() )
		{
			thePortInstance = getSymbolTable().searchPortConnectorPoint(
					(& theExecutable4Port), aComPoint.getPort());

			if( thePortInstance == nullptr )
			{
				incrErrorCount();
				AVM_OS_WARN
					<< aComPoint.errorLocation( aComPoint )
					<< "Unfound in the connector the port < "
					<< aComPoint.getPort().getFullyQualifiedNameID()
					<< " > in the model "
					<< str_header( aComPoint.getMachine() )
					<< std::endl;
			}
			else if( (not thePortInstance->getModifier().isVisibilityPublic())
					&& theExecutableOfConnector.isNTEQ(theExecutable4Port) )
			{
				incrErrorCount();
				AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
							<< "Unexpected a non-public port << "
							<< str_header( thePortInstance )
							<< " >> in a connector !"
							<< std::endl << std::endl;
			}
		}
		else //if( aComPoint.getPort().isComposite() )
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
						<< "Unexpected the COMPOSITE PORT << "
						<< str_header( thePortInstance )
						<< " >> in a connector !"
						<< std::endl << std::endl;

			return( false );
		}
	}
	else if( aComPoint.hasMachinePortQualifiedNameID() )
	{
		std::string portId;

		if( aComPoint.getMachinePortQualifiedNameID().is< Identifier >() )
		{
			portId = aComPoint.getMachinePortQualifiedNameID().str();
		}
		if( aComPoint.getMachinePortQualifiedNameID().
				is< QualifiedIdentifier >() )
		{
			portId = aComPoint.getMachinePortQualifiedNameID().
					to< QualifiedIdentifier >().getNameID();
		}
		else if( aComPoint.getMachinePortQualifiedNameID().
				is< UniFormIdentifier >() )
		{
			portId = aComPoint.getMachinePortQualifiedNameID().
					to< UniFormIdentifier >().toStringId();
		}
		else
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
					<< "Unfound in the connector the port < "
					<< aComPoint.getMachinePortQualifiedNameID()
					<< " > in the model of < "
					<< str_header( theExecutable4Port ) << " > !"
					<< std::endl;

			return( false );
		}

		std::string portUfi =
			theExecutable4Port.getAstFullyQualifiedNameID() + "." + portId;

		thePortInstance = getSymbolTable().searchPortConnectorPoint(
				(& theExecutable4Port), portUfi);

		if( thePortInstance == nullptr )
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
					<< "Unfound in the connector the port < "
					<< portUfi << " > in the model of < "
					<< str_header( aComPoint.getMachine() ) << " > !"
					<< std::endl;

			return( false );
		}
		else if( (not thePortInstance->getModifier().isVisibilityPublic())
				&& theExecutableOfConnector.isNTEQ(theExecutable4Port) )
		{
			incrErrorCount();
			AVM_OS_WARN << aComPoint.errorLocation( aComPoint )
						<< "Unexpected a non-public port << "
						<< str_header( thePortInstance )
						<< " >> in a connector !"
						<< std::endl << std::endl;
		}
	}

	return( thePortInstance != nullptr );
}



void CompilerOfInteraction::createRoutingData(
		List< RoutingData > & listOfRoutingData,
		ExecutableForm & theExecutable, InstanceOfConnector & aConnector,
		const ComRoute & aComRoute, const ComPoint & aComPoint)
{
	bool isInstanceStaticFlag = true;

	InstanceOfMachine * anInstanceStatic = nullptr;

	ExecutableForm * anExecutable4Port = compileComPointMachine(
			theExecutable, aComPoint, isInstanceStaticFlag, anInstanceStatic);
	if( anExecutable4Port != nullptr )
	{
		if( aComPoint.isMachineAllPort() )
		{
			do
			{
				for( const auto & itPort : anExecutable4Port->getPort() )
				{
					if( itPort.asPort().isSignal()
						|| (itPort.getContainer() == (& theExecutable)) )
					{
						if( itPort.getModifier().hasDirectionKind(
								aComRoute.getModifier().getDirectionKind() ) )
						{
							listOfRoutingData.append(
									addRoutingData(theExecutable,
											isInstanceStaticFlag, aConnector,
											(* anInstanceStatic),
											itPort.asPort(), aComRoute) );
						}
						else
						{
							incrWarningCount();
							AVM_OS_WARN << aComPoint.warningLocation(aComPoint)
								<< "Incompatibility between the ComRoute << "
								<< aComRoute.str() << " >> & the ComPoint << "
								<< str_header( itPort ) << " >> NATURE "
								<< std::endl << std::endl;
						}
					}
				}

				anExecutable4Port = anExecutable4Port->getExecutableContainer();
			}
			while( anExecutable4Port != nullptr );
		}
		else
		{
			InstanceOfPort * aPortInstance = nullptr;

			if( compileComPointPort(theExecutable,
					(* anExecutable4Port), aComPoint, aPortInstance) )
			{
				if( aPortInstance->getModifier().isDirectionKind(
						aComRoute.getModifier().getDirectionKind() )
					|| aPortInstance->getModifier().isDirectionInout() )
				{
					listOfRoutingData.append(
							addRoutingData(
									theExecutable, isInstanceStaticFlag,
									aConnector, (* anInstanceStatic),
									(* aPortInstance), aComRoute ) );
				}
				else
				{
					incrWarningCount();
					AVM_OS_WARN << aComPoint.warningLocation( aComPoint )
							<< "Incompatibility between the ComRoute << "
							<< aComRoute.str() << " >> & the ComPoint << "
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
	const InstanceOfMachine & aMachine = aRouter.getMachine();

	for( const auto & itPort : aMachine.refExecutable().getPort() )
	{
		if( itPort.asPort().isPort()
			&& itPort.getModifier().isnotVisibilityPublic()
			&& aMachine.getSpecifier().isnotComponentSystem() )
		{
			if( itPort.getModifier().hasDirectionInput()
				&& aRouter.hasnoInputRouting( itPort.getRouteOffset() ) )
			{
				aRouter.setInputRouting(itPort.getRouteOffset(),
						RoutingData(0, aMachine, itPort.asPort(),
								ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );

				// ERROR REPORTING
				incrErrorCount();
				itPort.getAstElement().errorLocation(AVM_OS_WARN)
						<< "Unexpected a input port << "
						<< itPort.getFullyQualifiedNameID()
						<< " >> without routing data in the router of the "
							"machine << " << aMachine.getFullyQualifiedNameID()
						<< " >> "
						<< std::endl;
			}
			// NO ELSE because of INOUT PORT
			if( itPort.getModifier().hasDirectionOutput()
				&& aRouter.hasnoOutputRouting( itPort.getRouteOffset() ) )
			{
				aRouter.setOutputRouting(itPort.getRouteOffset(),
						RoutingData(0, aMachine, itPort.asPort(),
								ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );

				// ERROR REPORTING
				incrErrorCount();
				itPort.getAstElement().errorLocation(AVM_OS_WARN)
						<< "Unexpected an output port << "
						<< itPort.getFullyQualifiedNameID()
						<< " >> without routing data in the router of the "
							"machine << " << aMachine.getFullyQualifiedNameID()
						<< " >> "
						<< std::endl;
			}
		}
	}
}


void CompilerOfInteraction::updateGlobalRoute(
		const Router & refRouter, const Router & newRouter)
{
	for( std::size_t offset = 0 ; offset < mNextRouteID ; ++offset )
	{
		if( newRouter.getInputRouting(offset).invalid() )
		{
			if( refRouter.hasInputRouting(offset) )
			{
				newRouter.setInputRouting(offset,
						refRouter.getInputRouting(offset));
			}
		}
		// NO ELSE because of INOUT PORT
		if( newRouter.hasnoOutputRouting(offset) )
		{
			if( refRouter.hasOutputRouting(offset) )
			{
				newRouter.setOutputRouting(offset,
						refRouter.getOutputRouting(offset));
			}
		}
	}
}

void CompilerOfInteraction::updateLocalModelUsingLocalPrototype(
		ExecutableForm & theExecutable, const Router & aRouter4Model)
{
	const InstanceOfMachine & aMachine = aRouter4Model.getMachine();

//!@?DEBUG:
//AVM_OS_TRACE << "updateLocalModelUsingLocalPrototype: "
//		<< theExecutable.getFullyQualifiedNameID() << std::endl
//		<< " >>==>> " << str_header( aMachine ) << std::endl;
//AVM_OS_TRACE << "INIT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);

	if( aMachine.getSpecifier().isDesignPrototypeStatic() )
	{
		const Router & aRouter4Prototype =
				theExecutable.getRouter4Prototype(aMachine);

//!@?DEBUG:
//aRouter4Prototype.toStream(AVM_OS_TRACE);
//aRouter4Model.toStream(AVM_OS_TRACE);

		// UPDATE GLOBAL ROUTE
		updateGlobalRoute(aRouter4Prototype, aRouter4Model);

//!@?DEBUG:
//AVM_OS_TRACE << "AVANT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);

		for( const auto & itPort : aMachine.refExecutable().getPort() )
		{
			if( itPort.getModifier().hasDirectionInput()
				&& aRouter4Model.getInputRouting(
						itPort.getRouteOffset()).invalid() )
			{
				if( aRouter4Prototype.getInputRouting(
						itPort.getRouteOffset()).valid() )
				{
					aRouter4Model.setInputRouting(itPort.getRouteOffset(),
							aRouter4Prototype.getInputRouting(
									itPort.getRouteOffset()));
				}
			}
			// NO ELSE because of INOUT PORT
			if( itPort.getModifier().hasDirectionOutput()
				&& aRouter4Model.hasnoOutputRouting(
						itPort.getRouteOffset()) )
			{
				if( aRouter4Prototype.getOutputRouting(
						itPort.getRouteOffset()).valid() )
				{
					aRouter4Model.setOutputRouting(itPort.getRouteOffset(),
							aRouter4Prototype.getOutputRouting(
									itPort.getRouteOffset()));
				}
			}
		}

//!@?DEBUG:
//AVM_OS_TRACE << "APRES :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);
//AVM_OS_TRACE << std::endl;
	}
}


void CompilerOfInteraction::updateLocalModelUsingGlobalModel(
		const Router & aRouter4Model)
{
	const InstanceOfMachine & aMachine = aRouter4Model.getMachine();

	ExecutableForm & anExecutable =
			const_cast< ExecutableForm & >( aMachine.refExecutable() );

//!@?DEBUG:
//AVM_OS_TRACE << "updateLocalModelUsingGlobalModel: "
//		<< theExecutable.getFullyQualifiedNameID() << std::endl
//		<< " >>==>> " << str_header( aMachine ) << std::endl;
//AVM_OS_TRACE << "INIT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);

	Router aRouter4ModelThis;

	if( aMachine.getSpecifier().isDesignModel()
		&& anExecutable.hasRouter4Model() )
	{
		aRouter4ModelThis = anExecutable.getRouter4Model(& anExecutable);
	}
	else if( aMachine.getSpecifier().isDesignPrototypeStatic()
		&& anExecutable.hasRouter4Instance() )
	{
		aRouter4ModelThis = anExecutable.getRouter4This();
	}
	else if( not anExecutable.hasRouter4Instance() )
	{
		anExecutable.appendRouter4Instance( aRouter4Model );

		aRouter4ModelThis = anExecutable.getRouter4This();

		if( not anExecutable.hasRouter4Model() )
		{
			anExecutable.setRouters4Model(
					anExecutable.getRouters4Instance() );
		}
	}
	else if( not anExecutable.hasRouter4Model() )
	{
		anExecutable.setRouters4Model(
				anExecutable.getRouters4Instance() );
	}


	if( aRouter4ModelThis.valid() )
	{
//!@?DEBUG:
//aRouter4ModelThis.toStream(AVM_OS_TRACE);
//aRouter4Model.toStream(AVM_OS_TRACE);

		// UPDATE GLOBAL ROUTE
		updateGlobalRoute(aRouter4ModelThis, aRouter4Model);


//!@?DEBUG:
//AVM_OS_TRACE << "AVANT :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);

		for( const auto & itPort : aMachine.refExecutable().getPort() )
		{
			if( itPort.getModifier().hasDirectionInput()
				&& aRouter4Model.getInputRouting(
						itPort.getRouteOffset()).invalid() )
			{
				if( aRouter4ModelThis.getInputRouting(
						itPort.getRouteOffset()).valid() )
				{
					aRouter4Model.setInputRouting(itPort.getRouteOffset(),
							aRouter4ModelThis.getInputRouting(
									itPort.getRouteOffset()));
				}
				else if( itPort.asPort().isPort() )
				{
					aRouter4Model.setInputRouting(itPort.getRouteOffset(),
							RoutingData(0, aMachine, itPort.asPort(),
									ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
				}
			}
			// NO ELSE because of INOUT PORT
			if( itPort.getModifier().hasDirectionOutput()
				&& aRouter4Model.hasnoOutputRouting(
						itPort.getRouteOffset()) )
			{
				if( aRouter4ModelThis.getOutputRouting(
						itPort.getRouteOffset()).valid() )
				{
					aRouter4Model.setOutputRouting(itPort.getRouteOffset(),
							aRouter4ModelThis.getOutputRouting(
									itPort.getRouteOffset()));
				}
				else if( itPort.asPort().isPort() )
				{
					aRouter4Model.setOutputRouting(itPort.getRouteOffset(),
							RoutingData(0, aMachine, itPort.asPort(),
									ComProtocol::PROTOCOL_ENVIRONMENT_KIND) );
				}
			}
		}

//!@?DEBUG:
//AVM_OS_TRACE << "APRES :>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>" << std::endl;
//aRouter4Model.toStream(AVM_OS_TRACE);
//AVM_OS_TRACE << std::endl;
	}
	else
	{
		setUndefinedLocalRouteToEnv( aRouter4Model );
	}
}


void CompilerOfInteraction::postCompileCommunication(
		ExecutableForm & theExecutable)
{
	// UPDATE DEFAULT MODEL ROUTER TO ENVIRONMENT
	if( theExecutable.hasRouter4Model() )
	{
		for( const auto & itRouter : theExecutable.getRouters4Model() )
		{
			if( itRouter.valid() )
			{
				updateLocalModelUsingLocalPrototype(theExecutable, itRouter);

				updateLocalModelUsingGlobalModel( itRouter );

				updateGlobalRoute(theExecutable.getRouter4This(), itRouter);
			}
		}

		// UPDATE DEFAULT INSTANCE ROUTER USING THE MODEL'S
		TableOfRoutingData::const_iterator itRdModel;

		TableOfRoutingData::iterator itRdInst;
		TableOfRoutingData::iterator endRD;

		for( auto & itRouter : theExecutable.getRouters4Instance() )
		{
			if( itRouter.valid() )
			{
				const Router & theRouter = theExecutable.
						getRouter4Model(itRouter.getMachine());

				if( theRouter == itRouter )
				{
					continue;
				}

				else if( theRouter.valid() )
				{
					itRdModel = theRouter.getInputRoutingTable().begin();

					for( auto & itRdInst : itRouter.getInputRoutingTable() )
					{
						if( itRdInst.invalid() && (*itRdModel).valid() )
						{
							itRdInst = (*itRdModel);
						}
						// Increment for itModel
						++itRdModel;
					}


					itRdModel = theRouter.getOutputRoutingTable().begin();

					for( auto & itRdInst : itRouter.getOutputRoutingTable() )
					{
						if( itRdInst.invalid() && (*itRdModel).valid() )
						{
							itRdInst = (*itRdModel);
						}
						// Increment for itModel
						++itRdModel;
					}
				}
			}
		}
	}
	else
	{
		for( const auto & itRouter : theExecutable.getRouters4Instance() )
		{
			if( itRouter.valid() )
			{
				setUndefinedLocalRouteToEnv( itRouter );
			}
		}
	}
}



}
