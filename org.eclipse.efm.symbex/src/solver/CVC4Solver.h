/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_CVC4_H_
#define SOLVER_CVC4_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_CVC4_ )


#include <solver/api/SmtSolver.h>

#include <cvc4/expr/expr.h>
#include <cvc4/expr/expr_manager.h>
#include <cvc4/expr/type.h>
#include <cvc4/smt/smt_engine.h>

#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{


class WObject;

class ExecutionContext;
class ExecutionData;

class TypeSpecifier;


class CVC4Solver :
		public SmtSolver< CVC4::Expr , CVC4::Type , CVC4::Expr , false , true >

{

	AVM_DECLARE_UNCLONABLE_CLASS(CVC4Solver)

public:
	/*
	 ***************************************************************************
	 * ID
	 ***************************************************************************
	 */
	static std::string ID;

	static std::string DESCRIPTION;

	static avm_uint64_t SOLVER_SESSION_ID;

	static 	CVC4::Expr CVC4_EXPR_NULL;
	static 	CVC4::Type CVC4_TYPE_NULL;



protected:
	/**
	 * ATTRIBUTES
	 **/
	std::string mParamPrefix;

	CVC4::ExprManager mExprManager;
	CVC4::SmtEngine mSmtEngine;


public:
	/**
	* CONSTRUCTOR
	* Default
	*/
	CVC4Solver(bool produce_models_flag = false);

	/**
	* DESTRUCTOR
	*/
	virtual ~CVC4Solver();

	/**
	 * CONFIGURE
	 */
	virtual bool configure(
			Configuration & aConfiguration, WObject * wfFilterObject,
			ListOfPairMachineData & listOfSelectedVariable);


	/**
	 * PROVER
	 */
	virtual bool isSubSet(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	virtual bool isEqualSet(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	virtual SolverDef::SATISFIABILITY_RING isSatisfiable(const BF & aCondition);


	/**
	 * SOLVER
	 */
	virtual bool solveImpl(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);


	/**
	 * CREATE - DESTROY
	 * ValidityChecker
	 */
	bool createChecker();
	bool destroyChecker();
	bool resetTable();

	/**
	 * TOOLS
	 */
	void edToExpr(const ExecutionData & newED, CVC4::Expr & newFormula,
			const ExecutionData & oldED, CVC4::Expr & oldFormula);

	void edToExprWithVarEquality(const ExecutionData & newED,
			CVC4::Expr & newFormula, const ExecutionData & oldED,
			CVC4::Expr & oldFormula, CVC4::Expr & equFormula);

	CVC4::Expr  edToExpr(const ExecutionData & anED);

	CVC4::Expr safe_from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

	CVC4::Expr from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

	CVC4::Expr & getParameterExpr(const BF & aParameter);
	CVC4::Expr & getVariableExpr(InstanceOfData * aVar,
			CVC4::Type varType, avm_offset_t varID);

};


} /* namespace sep */

#endif /* _AVM_SOLVER_CVC4_ */


#endif /* SOLVER_CVC4_H_ */

