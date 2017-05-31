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
class InstanceOfConnect;
class InstanceOfMachine;
class InstanceOfPort;
class PropertyPart;


class CompilerOfInteraction  :  public BaseCompiler
{

protected:
	/*
	 * ATTRIBUTES
	 */
	avm_size_t mNextRouteID;

	avm_size_t mNextConnectID;

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
	 * mNextConnectID
	 */
	void updateMessageID()
	{
		mNextConnectID = mNextRouteID;
	}

	/**
	 ***************************************************************************
	 * PRE-COMPILATION
	 ***************************************************************************
	 */
	BF precompileParameter(ExecutableForm * aContainer,
			TableOfInstanceOfData & tableOfVariable,
			Variable * aParameter, avm_offset_t offset);

	void precompileComPoint(
			ExecutableForm * aContainer, PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);

	void precompileComPoint(ExecutableForm * aContainer,
			const PropertyPart::TableOfPort & listOfComPoint,
			avm_size_t ioPortOffset, TableOfInstanceOfData & tableOfVariable);

	void precompileChannel(
			ExecutableForm * aContainer, PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);

	void precompileBuffer(ExecutableForm * aContainer, Buffer * aBuffer);



	/**
	 ***************************************************************************
	 * COMPILATION
	 ***************************************************************************
	 */
	void compilePort(ExecutableForm * anExecutable);

	void compilePort(ExecutableForm * anExecutable,
			const InstanceOfPort & aPortInstance);


	Router addMachineModelRouter(
			ExecutableForm * theExecutable, InstanceOfMachine * aMachine);

	Router newMachineRouter(InstanceOfMachine * aMachine);


	void compileCommunication(ExecutableForm * theExecutable,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileConnector(ExecutableForm * theExecutable,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileConnector(ExecutableForm * theExecutable,
			Connector * aConnector, InstanceOfConnect * ioc,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);

	void compileRoute(ExecutableForm * theExecutable,
			Connector * aConnector, InstanceOfConnect * ioc,
			bool & hasSynchronizeMachine, bool & hasUpdateBuffer);



	void compileConnectorBroadcast(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorBuffer(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorRoutingCast(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorSynchronous(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorFlow(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorTransfert(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileConnectorEnvironment(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);


	void compileRouteBroadcast(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileRouteBuffer(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileRouteRoutingCast(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileRouteSynchronous(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileRouteTransfert(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);

	void compileRouteEnvironment(
			ExecutableForm * theExecutable, InstanceOfConnect * ioc);



	ExecutableForm * compileComPointMachine(
			ExecutableForm * theExecutable, ComPoint * aComPoint,
			bool & isInstanceStaticFlag, InstanceOfMachine * & aMachine);

	bool compileComPointPort(ExecutableForm * theExecutable4Port,
			ComPoint * aComPoint, InstanceOfPort * & aPort);

	void createRoutingData(List< RoutingData > & listOfRoutingData,
			ExecutableForm * theExecutable, InstanceOfConnect * ioc,
			ComRoute * aComRoute, ComPoint * aComPoint);

	RoutingData addRoutingData(ExecutableForm * theExecutable,
			bool isInstanceStaticFlag, InstanceOfConnect * ioc,
			InstanceOfMachine * theInstanceStatic,
			InstanceOfPort * thePortInstance,
			Modifier::DIRECTION_KIND aDirection);

	RoutingData addRoutingData(Router & theRouter,
			RoutingData & theRoutingData,
			Modifier::DIRECTION_KIND aDirection);


	/**
	 ***************************************************************************
	 * POST-COMPILATION
	 ***************************************************************************
	 */

	void setUndefinedLocalRouteToEnv(const Router & aRouter);

	void updateGlobalRoute(const Router & refRouter, const Router & newRouter);

	void updateLocalModelUsingLocalPrototype(
			ExecutableForm * theExecutable, const Router & aRouter4Model);

	void updateLocalModelUsingGlobalModel(const Router & aRouter4Model);

	void postCompileCommunication(ExecutableForm * theExecutable);

};


}

#endif /* BUILDER_COMPILER_COMPILEROFINTERACTION_H_ */
