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

#ifndef TRACENUMERIZER_H_
#define TRACENUMERIZER_H_

#include <fml/runtime/ExecutionData.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class ExecutionContext;
class EvaluationEnvironment;

class TraceManager;
class TracePoint;
class TraceSequence;


class TraceNumerizer
{

protected:
	/**
	 * ATTRIBUTES
	 */
	AVM_OPCODE mNumerizerOperator;

	SolverDef::SOLVER_KIND mSolverKind;

	EvaluationEnvironment & ENV;
	ExecutionData modelED;

	const ExecutionContext * aTraceEC;

	TraceSequence * aTraceElement;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceNumerizer(EvaluationEnvironment & anENV)
	: mNumerizerOperator( AVM_OPCODE_CHECK_SAT ),
	mSolverKind( SolverDef::SOLVER_UNDEFINED_KIND ),
	ENV( anENV ),
	modelED( ),

	aTraceEC( nullptr ),
	aTraceElement( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceNumerizer()
	{
		//!! NOTHING
	}

	/**
	 * SETTER
	 */
	inline void setSolverKing(SolverDef::SOLVER_KIND aSolverKind)
	{
		mSolverKind = aSolverKind;
	}

	void setNumerizer(AVM_OPCODE aNumerizerOperator = AVM_OPCODE_NOP)
	{
		mNumerizerOperator = aNumerizerOperator;
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(const WObject * wfParameterObject);


	////////////////////////////////////////////////////////////////////////////
	// NUMERIZE API
	////////////////////////////////////////////////////////////////////////////

	void numerize(TraceManager & aTraceManager);

	void numerizeSolver(TraceManager & aTraceManager);
	void numerizeNewfresh(TraceManager & aTraceManager);
	void numerizeNothing(TraceManager & aTraceManager);

	void numerize(TraceSequence & aTraceElt);
	void numerize(TracePoint & aTracePoint);

};


} /* namespace sep */

#endif /* TRACENUMERIZER_H_ */
