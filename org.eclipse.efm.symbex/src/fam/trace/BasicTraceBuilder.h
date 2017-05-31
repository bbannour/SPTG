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

#include <fml/runtime/ExecutionContext.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class AvmTraceGenerator;
class EvaluationEnvironment;
class ExecutableSystem;
class ExecutionData;

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

	TraceManager * mTraceManager;

	SolverDef::SOLVER_KIND mSolverKind;

	TraceFilter & mTracePointFilter;

	bool mStepBeginSeparatorFlag;
	bool mStepEndSeparatorFlag;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	TraceSequence * aTraceElement;
	TracePoint * aTracePoint;
	BF bfTP;
	avm_size_t TP_ID;

	ListOfConstExecutionContext mTraceCache;

	const ExecutionContext * aRootEC;
	const ExecutionContext * aTraceEC;
	ListOfConstExecutionContext::const_iterator itEC;
	ListOfConstExecutionContext::const_iterator endEC;

	BF code;
	BaseCompiledForm * object;
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

	virtual bool configureImpl(WObject * wfParameterObject);


	////////////////////////////////////////////////////////////////////////////
	// CONSTRUCTION API
	////////////////////////////////////////////////////////////////////////////

	void build(TraceManager & aTraceManager);

	void build(const ExecutionContext & anEC);

	void buildTrace();

	void buildTraceVariable(const ExecutionContext & anEC,
			TraceSequence * aTraceElt, bool isnotRoot = true);

	void buildTraceIO(const ExecutionContext & anEC,
			TraceSequence * aTraceElt, const BF & ioTrace);

	void buildTraceRunnable(const ExecutionContext & anEC,
			TraceSequence * aTraceElt, const BF & aTrace);

	void printInitializationValues();

};


} /* namespace sep */

#endif /* BASICTRACEBUILDER_H_ */
