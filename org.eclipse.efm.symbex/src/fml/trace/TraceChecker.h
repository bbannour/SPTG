/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACECHECKER_H_
#define TRACECHECKER_H_

#include <fml/operator/OperatorLib.h>

#include <fml/lib/ITracePoint.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class AvmCode;
class BF;
class EvaluationEnvironment;
class ExecutableForm;
class ExecutionContext;
class TracePoint;



class TraceChecker
{

protected:
	EvaluationEnvironment & ENV;
	ExecutableForm * theLocalExecutableForm;

	SolverDef::SOLVER_KIND theSolverKind;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceChecker(EvaluationEnvironment & anENV)
	: ENV( anENV ),
	theLocalExecutableForm( NULL ),
	theSolverKind( SolverDef::DEFAULT_SOLVER_KIND )
	{
		//!! NOTHING
	}

	TraceChecker(EvaluationEnvironment & anENV, SolverDef::SOLVER_KIND aSolver)
	: ENV( anENV ),
	theLocalExecutableForm( NULL ),
	theSolverKind( aSolver )
	{
		//!! NOTHING
	}

	TraceChecker(EvaluationEnvironment & anENV, ExecutableForm * anExecutable)
	: ENV( anENV ),
	theLocalExecutableForm( anExecutable ),
	theSolverKind( SolverDef::DEFAULT_SOLVER_KIND )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceChecker()
	{
		//!! NOTHING
	}

	/**
	 * SETTER
	 * theSolverKind
	 */
	void setSolverKind(SolverDef::SOLVER_KIND aSolverKind)
	{
		theSolverKind = aSolverKind;
	}


	/**
	 * TEST
	 * TracePoint Nature
	 */
	bool isPointNature(const BF & arg,
			ENUM_TRACE_POINT::TRACE_NATURE nature) const;


	////////////////////////////////////////////////////////////////////////////
	// SAT CHECKING API
	////////////////////////////////////////////////////////////////////////////

	bool isSat(const ExecutionContext & anEC, const BF & arg);
	bool isSat(const ExecutionContext & anEC, const AvmCode & aCode);
	bool isSat(const ExecutionContext & anEC, AVM_OPCODE anOp, const BF & arg);

	bool isSat(const ExecutionContext & anEC, TracePoint * aTP);

	bool isSatFormula(const ExecutionContext & anEC, TracePoint * aTP);

	bool isSatTime(const ExecutionContext & anEC, TracePoint * aTP);
	bool isSatVariable(const ExecutionContext & anEC, TracePoint * aTP);


	bool isSatCom(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatRunnable(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatRoutine(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatTransition(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatState(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatStatemachine(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);

	bool isSatMachine(const ExecutionContext & anEC,
			TracePoint * aTP, const BF & aTrace);


	////////////////////////////////////////////////////////////////////////////
	// WILL NEVER SAT CHECKING API
	////////////////////////////////////////////////////////////////////////////

	bool willNeverSat(const ExecutionContext & anEC, const BF & arg);

	bool willNeverSat(const ExecutionContext & anEC, AvmCode * aCode);

	bool willNeverSat(
			const ExecutionContext & anEC, AVM_OPCODE anOp, const BF & arg);

	bool willNeverSat(const ExecutionContext & anEC, TracePoint * aTP);

	bool willNeverSatTransition(
			const ExecutionContext & anEC, TracePoint * aTP);

	bool willNeverSatState(
			const ExecutionContext & anEC, TracePoint * aTP);

	bool willNeverSatStatemachine(
			const ExecutionContext & anEC, TracePoint * aTP);

	bool willNeverSatMachine(
			const ExecutionContext & anEC, TracePoint * aTP);


};

} /* namespace sep */

#endif /* TRACECHECKER_H_ */
