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

#ifndef BUILDER_COMPILER_COMPILEROFINTERACTION_H_
#define BUILDER_COMPILER_COMPILEROFINTERACTION_H_

#include <builder/compiler/BaseCompiler.h>

#include <collection/List.h>

#include <fml/executable/Router.h>
#include <fml/executable/RoutingData.h>

#include <fml/infrastructure/PropertyPart.h>


namespace sep
{


class Compiler;

class Buffer;
class ComPoint;
class ComRoute;
class Connector;
class ExecutableForm;
class InstanceOfConnector;
class InstanceOfMachine;
class InstanceOfPort;
class PropertyPart;


class CompilerOfInteraction  :  public BaseCompiler
{

protected:
	/*
	 * ATTRIBUTES
	 */
	std::size_t mNextRouteID;

	std::size_t mNextConnectorID;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompilerOfInteraction(Compiler & aCompiler);


	/**
	 * DESTRUCTOR
	 */
	virtual ~CompilerOfInteraction()
	{
		//!! NOTHING
	}


	/**
	 * mNextRouteID
	 * mNextConnectorID
	 */
	void updateMessageID()
	{
		mNextConnectorID = mNextRouteID;
	}

	/**
	 ***************************************************************************
	 * PRE-COMPILATION
	 ***************************************************************************
	 */
	BF precompileParameter(ExecutableForm & aContainer,
			TableOfInstanceOfData & tableOfVariable,
			const Variable & aParameter, avm_offset_t offset);

	void precompileComPoint(
			ExecutableForm & aContainer, const PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);

	void precompileComPoint(ExecutableForm & aContainer,
			const PropertyPart::TableOfPort & listOfComPoint,
			std::size_t ioPortOffset, TableOfInstanceOfData & tableOfVariable);

	void precompileChannel(
			ExecutableForm & aContainer, const PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);

	void precompileBuffer(ExecutableForm & aContainer, const Buffer & aBuffer);



	/**
	 ***************************************************************************
	 * COMPILATION
	 ***************************************************************************
	 */
	void compilePort(ExecutableForm & anExecutable);

	void compilePort(ExecutableForm & anExecutable,
			const InstanceOfPort & aPortInstance);


	Router addMachineModelRouter(
			ExecutableForm & theExecutable,
			const InstanceOfMachine & aMachine);

	Router newMachineRouter(const InstanceOfMachine & aMachine);


	void compileCommunication(ExecutableForm & theExecutable,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileConnector(ExecutableForm & theExecutable,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileConnector(ExecutableForm & theExecutable,
			const Connector & astConnector, InstanceOfConnector & aConnector,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileRoute(ExecutableForm & theExecutable,
			const Connector & astConnector, InstanceOfConnector & aConnector,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);



	void compileConnectorBroadcast(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorBuffer(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorRoutingCast(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorSynchronous(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorFlow(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorTransfert(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileConnectorEnvironment(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);


	void compileRouteBroadcast(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileRouteBuffer(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileRouteRoutingCast(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileRouteSynchronous(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileRouteTransfert(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);

	void compileRouteEnvironment(
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector);



	ExecutableForm * compileComPointMachine(
			ExecutableForm & theExecutable, const ComPoint & aComPoint,
			bool & isInstanceStaticFlag, InstanceOfMachine * & aMachine);

	bool compileComPointPort(
			ExecutableForm & theExecutableOfConnector,
			ExecutableForm & theExecutable4Port,
			const ComPoint & aComPoint, InstanceOfPort * & aPort);

	void createRoutingData(List< RoutingData > & listOfRoutingData,
			ExecutableForm & theExecutable, InstanceOfConnector & aConnector,
			const ComRoute & aComRoute, const ComPoint & aComPoint);

	RoutingData addRoutingData(ExecutableForm & theExecutable,
			bool isInstanceStaticFlag, InstanceOfConnector & aConnector,
			const InstanceOfMachine & theInstanceStatic,
			const InstanceOfPort & thePortInstance, const ComRoute & aComRoute);

	RoutingData addRoutingData(
			InstanceOfConnector & aConnector, Router & theRouter,
			RoutingData & theRoutingData, const ComRoute & aComRoute);


	/**
	 ***************************************************************************
	 * POST-COMPILATION
	 ***************************************************************************
	 */

	void setUndefinedLocalRouteToEnv(const Router & aRouter);

	void updateGlobalRoute(const Router & refRouter, const Router & newRouter);

	void updateLocalModelUsingLocalPrototype(
			ExecutableForm & theExecutable, const Router & aRouter4Model);

	void updateLocalModelUsingGlobalModel(const Router & aRouter4Model);

	void postCompileCommunication(ExecutableForm & theExecutable);

};


}

#endif /* BUILDER_COMPILER_COMPILEROFINTERACTION_H_ */
