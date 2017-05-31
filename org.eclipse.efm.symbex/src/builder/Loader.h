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

public:
	/**
	 * TYPEDEF
	 */
	typedef List< RuntimeID >::const_iterator  const_rid_iterator;

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
	 * mOnCreateRoutime
	 */
	inline bool hasOnCreateRoutime() const
	{
		return( mOnCreateRoutime.nonempty() );
	}

	inline void resetOnCreateRoutime()
	{
		mOnCreateRoutime.clear();
	}

	/**
	 * [ CONST ] ITERATOR
	 */
	inline const_rid_iterator on_create_begin() const
	{
		return( mOnCreateRoutime.begin() );
	}

	inline const_rid_iterator on_create_end() const
	{
		return( mOnCreateRoutime.end() );
	}


	/**
	 * RUNNING onCREATE
	 * mOnCreateRoutime
	 */
	bool finalizeRunningOnCreate(
			const BaseEnvironment & ENV, APExecutionData & anED);

	/**
	 * UTILS
	 */
	BFCode loadSchedulerCode(
			APExecutionData & anED, const RuntimeForm & aRF,
			const BFCode & aSchedulerCode, bool isStaticLoading);

	void loadSchedulerCode(APExecutionData & anED,
			const RuntimeForm & aRF, const BFCode & aSchedulerCode,
			BFCode & loadCode, bool isStaticLoading);


	RuntimeForm * loadSystemInstance(APExecutionData & anED,
			const RuntimeID & aParentRID, InstanceOfMachine * aMachine,
			int & thePid, avm_offset_t & theOffset);

	RuntimeForm * loadMachineInstance(APExecutionData & anED,
			const RuntimeID & aParentRID, InstanceOfMachine * aMachine,
			int & thePid, avm_offset_t & theOffset);


	void loadMachine(APExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID, int & thePid,
			avm_offset_t & theOffset);

	RuntimeForm * dynamicLoadMachine(APExecutionData & anED,
			const RuntimeID & aRID, RuntimeForm * aModelRF,
			const RuntimeID & aParentRID, Operator * aScheduleOp);

	RuntimeForm * dynamicLoadMachine(APExecutionData & anED,
			const RuntimeID & aRID, InstanceOfMachine * anInstanceDynamic,
			const RuntimeID & aParentRID, Operator * aScheduleOp);


//	void loadInitialMonitorData(
//			APExecutionData & anED, const RuntimeID & aRID,
//			InstanceOfMachine * anInstanceMachine, bool isRecursive);


	bool loadData(APExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & aDataRID);

	bool loadBuffer(APExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID);


	const Router & getRouter4Model(
			APExecutionData & anED, RuntimeID & aRoutingRID);

	bool loadRouter(APExecutionData & anED, const RuntimeID & aRID,
			const RuntimeID & loadMachineRID);

	bool dynamicLoadRouter(APExecutionData & anED,
			const RuntimeID & loadMachineRID);

};


}

#endif /*LOADER_H_*/
