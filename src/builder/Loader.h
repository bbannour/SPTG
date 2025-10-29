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
#ifndef LOADER_H_
#define LOADER_H_

#include <common/BF.h>

#include <collection/List.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{

class AvmPrimitiveProcessor;

class BaseEnvironment;
class Builder;

class Configuration;

class ExecutableForm;

class InstanceOfData;
class InstanceOfMachine;

class RuntimeForm;

class Loader
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Configuration & mConfiguration;

	Builder & mBuilder;

	EvaluationEnvironment ENV;

	List< RuntimeID > mOnCreateRoutime;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Loader(Configuration & aConfiguration, Builder & aBuilder,
			AvmPrimitiveProcessor & aPrimitiveProcessor);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Loader()
	{
		//!! NOTHING
	}

	/**
	 * CONFIGURE
	 */
	bool configure();


	/**
	 * GETTER - TESTER
	 * mOnCreateRoutime
	 */
	inline List< RuntimeID > getOnCreateRoutime() const
	{
		return( mOnCreateRoutime );
	}

	inline bool hasOnCreateRoutime() const
	{
		return( mOnCreateRoutime.nonempty() );
	}

	inline void resetOnCreateRoutime()
	{
		mOnCreateRoutime.clear();
	}


	/**
	 * RUNNING onCREATE
	 * mOnCreateRoutime
	 */
	bool finalizeRunningOnCreate(
			const BaseEnvironment & ENV, ExecutionData & anED);

	/**
	 * UTILS
	 */
	BFCode loadSchedulerCode(
			ExecutionData & anED, const RuntimeForm & aRF,
			const BFCode & aSchedulerCode, bool isStaticLoading);

	void loadSchedulerCode(ExecutionData & anED,
			const RuntimeForm & aRF, const BFCode & aSchedulerCode,
			BFCode & loadCode, bool isStaticLoading);

	void setRuntimeSchedulerCode(ExecutionData & anED, RuntimeForm & aRF,
			const ExecutableForm & anExecutable, bool isStaticLoading);


	RuntimeForm * loadSystemInstance(ExecutionData & anED,
			const RuntimeID & aParentRID, InstanceOfMachine * aMachine,
			int & thePid, avm_offset_t & theOffset);

	RuntimeForm * loadMachineInstance(ExecutionData & anED,
			const RuntimeID & aParentRID, InstanceOfMachine * aMachine,
			int & thePid, avm_offset_t & theOffset);


	void loadMachine(ExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID, int & thePid,
			avm_offset_t & theOffset);

	RuntimeForm * dynamicLoadMachine(ExecutionData & anED,
			const RuntimeID & aRID, RuntimeForm * aModelRF,
			const RuntimeID & aParentRID, const Operator * aScheduleOp);

	RuntimeForm * dynamicLoadMachine(ExecutionData & anED,
			const RuntimeID & aRID, InstanceOfMachine * anInstanceDynamic,
			const RuntimeID & aParentRID, const Operator * aScheduleOp);


//	void loadInitialMonitorData(
//			ExecutionData & anED, const RuntimeID & aRID,
//			InstanceOfMachine * anInstanceMachine, bool isRecursive);


	bool loadData(ExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & aDataRID);

	bool loadBuffer(ExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID);


	const Router & getRouter4Model(
			ExecutionData & anED, RuntimeID & aRoutingRID);

	bool loadRouter(ExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID);

	bool dynamicLoadRouter(ExecutionData & anED,
			const RuntimeID & loadMachineRID);

};


}

#endif /*LOADER_H_*/
