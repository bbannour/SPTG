/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASICTRACEBUILDER_H_
#define BASICTRACEBUILDER_H_

#include "AbstractTraceBuilder.h"

#include <collection/Typedef.h>

#include <fml/lib/ITracePoint.h>
#include <fml/runtime/ExecutionContext.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class AvmTraceGenerator;
class EvaluationEnvironment;
class ExecutableSystem;
class ExecutionData;

class ObjectElement;

class TraceFilter;
class TraceManager;
class TracePoint;
class TraceSequence;


class BasicTraceBuilder  :  public AbstractTraceBuilder
{

protected:
	/**
	 * ATTRIBUTES
	 */
	EvaluationEnvironment & ENV;

	bool isSDLFlag;
	bool printInitValuesFlag;

	// Leaf position flag
	bool isLeafAtHeaderPositionFlag;

	ExecutionContextFlags::FAM_VERDICT pathSelectionVerdict;

	TraceManager * mTraceManager;

	SolverDef::SOLVER_KIND mSolverKind;

	TraceFilter & mTracePointFilter;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	TraceSequence * aTraceSequence;
	TracePoint * aTracePoint;
	BF bfTP;
	std::size_t TP_ID;

	ListOfConstExecutionContext mTraceCache;

	const ExecutionContext * aRootEC;
	const ExecutionContext * aTraceEC;
	ListOfConstExecutionContext::const_iterator itEC;
	ListOfConstExecutionContext::const_iterator endEC;

	BF code;
	ObjectElement * object;
	BF value;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasicTraceBuilder(AvmTraceGenerator & aProcessor,
			SolverDef::SOLVER_KIND aSolverKind,
			TraceFilter & aTracePointFilter);

	/**
	 * DESTRUCTOR
	 */
	virtual ~BasicTraceBuilder()
	{
		//!! NOTHING
	}



	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl(const WObject * wfParameterObject) override;

	////////////////////////////////////////////////////////////////////////////
	// CONSTRUCTION API
	////////////////////////////////////////////////////////////////////////////

	virtual void build(TraceManager & aTraceManager,
			const ListOfExecutionContext & rootECs) override;

	void build(const ExecutionContext & anEC);

	virtual void buildTrace();

	void buildTraceLeaf();

	void buildTraceNodeCondition(const ExecutionContext & anEC);

	void buildTraceCondition(const ExecutionContext & anEC,
			ENUM_TRACE_POINT::TRACE_NATURE aNature, const BF & aCondition);

	void buildTraceBuffer(const ExecutionContext & anEC, bool isnotRoot = true);

	virtual void buildTraceVariable(
			const ExecutionContext & anEC, bool isnotRoot = true);

	void buildTraceIO(const ExecutionContext & anEC,
			TraceSequence * aTraceElt, const BF & ioTrace);

	void buildTraceRunnable(const ExecutionContext & anEC,
			TraceSequence * aTraceElt, const BF & aTrace);

	void buildTraceInformation(
			const ExecutionContext & anEC, TraceSequence * aTraceElt);

	void printInitializationValues();

};


} /* namespace sep */

#endif /* BASICTRACEBUILDER_H_ */
