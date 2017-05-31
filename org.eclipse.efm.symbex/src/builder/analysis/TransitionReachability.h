/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRANSITIONREACHABILITY_H_
#define TRANSITIONREACHABILITY_H_

#include <collection/List.h>
#include <collection/Typedef.h>

#include <fml/buffer/LifoBuffer.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/InstanceOfBuffer.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TraceSequence.h>


namespace sep
{

class OutStream;
class AvmTransition;

class ExecutableForm;
class ExecutionContext;
class ExecutionData;

class InstanceOfPort;

class RuntimeForm;
class RuntimeID;

class TracePoint;


class TransitionReachability
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef List< ListOfAvmTransition > ListOfListOfAvmTransition;


	/**
	 * ATTRIBUTE
	 */
	const ExecutionContext & theEC;
	const ExecutionData & theED;
	RuntimeID theRID;
	AvmTransition * theTransition;

	TracePoint * theTransitionPoint;
	TraceSequence theTraceElement;

	avm_size_t theRuntimePathComputingCountLimit;

	bool theGoalAchievedFlag;

	InstanceOfBuffer theVirtualBuffer;
	LifoBuffer theEmitOutput;

	TableOfRuntimeFormState theTableOfRuntimeStatus;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TransitionReachability(const ExecutionContext & anEC,
			const RuntimeID & aRID, AvmTransition * aTransition);


	/**
	 * UTILS
	 */
	bool initialize();

	bool computePath();

	bool computePath(TraceSequence & aTraceElement);

	void report(OutStream & os);


	bool computePath(const RuntimeID & aRID, AvmTransition * aTransition);

	bool fireTransition(const RuntimeID & aRID, AvmTransition * aTransition);

	void traceTransition(const RuntimeID & aRID, AvmTransition * aTransition);

	bool computePathToTransition(
			const RuntimeID & aRID, AvmTransition * aTransition);

	bool computePathFromRunnable(
			const RuntimeID & aRID, AvmTransition * aTransition);

	bool computePathToInput(
			const RuntimeID & aRID, InstanceOfPort * anInputTrace);


	bool computePathToTransition(const RuntimeID & aRID,
			AvmTransition * aTransition, ListOfAvmTransition & oneTransitionPath);

	bool computePathToTransition(const RuntimeID & aRID,
			AvmTransition * aTransition, ListOfListOfAvmTransition & allTransitionPaths);

	bool computeTargetMachine(RuntimeID & aRID, AvmCode * aCode);

};


} /* namespace sep */

#endif /* TRANSITIONREACHABILITY_H_ */
