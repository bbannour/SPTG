/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_SOLVERFACTORY_H_
#define SOLVER_SOLVERFACTORY_H_

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class Element;
class BF;

class EvaluationEnvironment;

class InstanceOfData;

class OutStream;

class SatSolver;


class SolverFactory
{

public:
	/**
	 * ATTRIBUTE
	 */
	static SatSolver * theDefaultSolver4CheckSatisfiability;
	static SatSolver * theDefaultSolver4ModelsProduction;

	static BFVector thePCParameters;
	static BFVector thePCParameterValues;

	////////////////////////////////////////////////////////////////////////////
	// Pour pouvoir reutiliser tout l'outillage de Diverity
	static ExecutionData theSymbolicED;


public:
	/**
	 * LOADER - DISPOSER
	 * DESTROY
	 */
	static void load();
	static void dispose();

	static void destroy(SatSolver * aSolver);

	/**
	 * SOLVER API
	 */
	static SolverDef::SATISFIABILITY_RING isSatisfiable(
			SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition);

	inline static bool isStrongSatisfiable(
			SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition)
	{
		return( SolverFactory::isSatisfiable(aSolverKind, aCondition)
				== SolverDef::SATISFIABLE );
	}

	inline static bool isWeakSatisfiable(
			SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition)
	{
		return( SolverFactory::isSatisfiable(aSolverKind, aCondition)
				!= SolverDef::UNSATISFIABLE );
	}



	static SolverDef::SATISFIABILITY_RING isSatisfiable(
			const BF & aCondition, bool useDefaultSolver = false);

	inline static bool isStrongSatisfiable(
			const BF & aCondition, bool useDefaultSolver)
	{
		return( SolverFactory::isSatisfiable(aCondition, useDefaultSolver)
				== SolverDef::SATISFIABLE );
	}

	inline static bool isWeakSatisfiable(
			const BF & aCondition, bool useDefaultSolver)
	{
		return( SolverFactory::isSatisfiable(aCondition, useDefaultSolver)
				!= SolverDef::UNSATISFIABLE );
	}

	inline static bool isStrongSatisfiable(const BF & aCondition)
	{
		return( SolverFactory::isSatisfiable(aCondition,
			SolverDef::DEFAULT_SOLVER_USAGE_FLAG) == SolverDef::SATISFIABLE );
	}

	inline static bool isWeakSatisfiable(const BF & aCondition)
	{
		return( SolverFactory::isSatisfiable(aCondition,
			SolverDef::DEFAULT_SOLVER_USAGE_FLAG) != SolverDef::UNSATISFIABLE );
	}


	/**
	 * USED BY FAM LtlProverFilter
	 */
	static bool isEmptyIntersection(
			ListOfInstanceOfData aListOfVarParam,
			const ExecutionContext & aMainEC,
			const ExecutionContext & aComparEC);

	static bool isSubSet(
			const ExecutionContext & aMainEC,
			const ExecutionContext & aComparEC);


	/**
	 * SOLVER
	 */
	static SatSolver * newSolver4CheckSatisfiability(
			SolverDef::SOLVER_KIND aSolverKind);

	static SatSolver * newSolver4ModelsProduction(
			SolverDef::SOLVER_KIND aSolverKind);


	////////////////////////////////////////////////////////////////////////////
	// CONDITION PARAMETER SOLVING
	////////////////////////////////////////////////////////////////////////////

	static bool solve(SolverDef::SOLVER_KIND aSolverKind, const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);


	////////////////////////////////////////////////////////////////////////////
	// EXECUTION CONTEXT SOLVING
	////////////////////////////////////////////////////////////////////////////

	inline static ExecutionData solve(
			EvaluationEnvironment & ENV, const ExecutionContext & anEC)
	{
//		return( SolverFactory::solve(
//				SolverDef::DEFAULT_SOLVER_KIND, ENV, anEC) );

		return( SolverFactory::solve(
				(*theDefaultSolver4ModelsProduction), ENV, anEC) );
	}

	inline static ExecutionData solve(SolverDef::SOLVER_KIND aSolverKind,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC)
	{
		return( SolverFactory::solve(aSolverKind, ENV, anEC,
				anEC.getExecutionData().getAllPathCondition()) );
	}

	static ExecutionData solve(SolverDef::SOLVER_KIND aSolverKind,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC,
			const BF & aCondition);


	inline static ExecutionData solve(SatSolver & aSolver,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC)
	{
		ExecutionData anED = anEC.getExecutionData();
		return( SolverFactory::solve(aSolver, ENV, anED) ?
				anED : ExecutionData::_NULL_);
	}

	inline static ExecutionData solve(SatSolver & aSolver,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC,
			const BF & aCondition)
	{
		ExecutionData anED = anEC.getExecutionData();

		return( SolverFactory::solve(aSolver, ENV, anED, aCondition) ?
				anED : ExecutionData::_NULL_);
	}


	////////////////////////////////////////////////////////////////////////////
	// EXECUTION DATA SOLVING
	////////////////////////////////////////////////////////////////////////////

	inline static bool solve(
			EvaluationEnvironment & ENV, ExecutionData & anED)
	{
		return( SolverFactory::solve(
				(*theDefaultSolver4ModelsProduction), ENV, anED) );
	}

	inline static bool solve(SatSolver & aSolver,
			EvaluationEnvironment & ENV, ExecutionData & anED)
	{
		return( SolverFactory::solve(aSolver, ENV, anED,
				anED.getAllPathCondition()) );
	}

	static bool solve(SatSolver & aSolver, EvaluationEnvironment & ENV,
			ExecutionData & anED, const BF & aCondition);


	////////////////////////////////////////////////////////////////////////////
	// EXECUTION CONTEXT NUMERIZATION
	////////////////////////////////////////////////////////////////////////////

	inline static ExecutionContext * numerize(
			EvaluationEnvironment & ENV, const ExecutionContext & anEC)
	{
		return( SolverFactory::numerize(
				(*theDefaultSolver4ModelsProduction), ENV, anEC) );
	}

	inline static ExecutionContext * numerize(SatSolver & aSolver,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC)
	{
		ExecutionData newED = SolverFactory::solve(aSolver, ENV, anEC);

		// ATTENTION : Hauteur à modifier !!!
		return( new ExecutionContext(anEC, newED, anEC.getHeight() + 1, 0) );
	}



	////////////////////////////////////////////////////////////////////////////
	// EXECUTION CONTEXT PARAMETERS NUMERIZATION
	////////////////////////////////////////////////////////////////////////////

	inline static bool solveParameters(ExecutionData & anED)
	{
		return( solveParameters(anED, anED.getAllPathCondition()) );
	}

	static bool solveParameters(ExecutionData & anED, const BF & aCondition);


	////////////////////////////////////////////////////////////////////////////
	// Pour pouvoir reutiliser tout l'outillage de DIVERSITY
	////////////////////////////////////////////////////////////////////////////

	static void setModel(EvaluationEnvironment & ENV, ExecutionData & anED);
	static void resetModel(ExecutionData & anED);

	static void setRuntimeParametersSolvingValues(ExecutionData & anED);
	static void updateRuntimeParametersValues(const BF & aValue);

	static void finalizeRuntimeParameters();


	////////////////////////////////////////////////////////////////////////////
	// EXECUTION DATA NEWFRESH
	////////////////////////////////////////////////////////////////////////////

	static ExecutionData solveNewfresh(SolverDef::SOLVER_KIND aSolverKind,
			EvaluationEnvironment & ENV, const ExecutionContext & anEC,
			const BF & aCondition);


	////////////////////////////////////////////////////////////////////////////
	// TO_SMT
	////////////////////////////////////////////////////////////////////////////

	static bool to_smt(OutStream & os, const BF & aCondition,
			SolverDef::SOLVER_KIND aSolverKind = SolverDef::SOLVER_Z3_KIND);



};



}

#endif /* SOLVER_SOLVERFACTORY_H_ */
