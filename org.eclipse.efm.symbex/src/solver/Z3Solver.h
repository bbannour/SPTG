/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 févr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_Z3_H_
#define SOLVER_Z3_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_Z3_ ) and (not defined( _AVM_SOLVER_Z3_C_ ))

#include <solver/api/SmtSolver.h>

#include <z3++.h>

#include <common/BF.h>

#include <collection/BFContainer.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{

class WObject;


class Z3Solver :
		public SmtSolver< z3::symbol , z3::sort , z3::expr , false , false >
{

	AVM_DECLARE_UNCLONABLE_CLASS(Z3Solver)


public:
	/*
	 ***************************************************************************
	 * ID
	 ***************************************************************************
	 */
	static std::string ID;

	static std::string DESCRIPTION;

	static std::uint64_t SOLVER_SESSION_ID;


protected:
	/**
	 * ATTRIBUTES
	 **/
	z3::config  * CONFIG;

	z3::context * CONTEXT;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Z3Solver();

	/**
	 * DESTRUCTOR
	 */
	virtual ~Z3Solver()
	{
		//!! NOTHING
	}


	/**
	 * CONFIGURE
	 */
	static bool configure(const WObject * wfFilterObject);


	/**
	 * PROVER
	 */
	virtual bool isSubSet(
			const ExecutionContext & newEC, const ExecutionContext & oldEC) override;

	virtual bool isEqualSet(
			const ExecutionContext & newEC, const ExecutionContext & oldEC) override;

	virtual SolverDef::SATISFIABILITY_RING isSatisfiable(const BF & aCondition) override;


	/**
	 * SOLVER
	 */
	virtual bool solveImpl(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector) override;


	/**
	 * CREATE - DESTROY
	 * ValidityChecker
	 */
	bool createChecker(z3::config & cfg, z3::context & ctx);
	bool destroyChecker() override;
	bool resetTable() override;

	/**
	 * TOOLS
	 */

	z3::sort getZ3Type(const BaseTypeSpecifier & bts);

	z3::expr getParameterExpr(const BF & bParameter);
	z3::expr getVariableExpr(InstanceOfData * aVar, std::size_t varID);

	z3::expr getBoundParameterExpr(const BF & bParameter, z3::expr & z3And);

	void appendPossitiveAssertion(z3::solver & z3Solver);

	z3::expr safe_from_baseform(const BF & exprForm);

	z3::expr from_baseform(const BF & exprForm);

	BF to_baseform(z3::model z3Model, z3::expr z3Form);


	/**
	 * Using file API
	 */

	virtual SolverDef::SATISFIABILITY_RING smt_check_sat(const BF & aCondition);

	virtual bool smt_check_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual SolverDef::SATISFIABILITY_RING from_smt_sat(const BF & aCondition);

	virtual bool from_smt_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual bool to_smt(OutStream & os,
			const BF & exprForm, BFVector & dataVector) const;

	virtual void dbg_smt(z3::solver & z3Solver, bool produceModelOption = false) const;

};


} /* namespace sep */


#elif defined( _AVM_SOLVER_Z3_C_ )

#define _AVM_SOLVER_Z3_

#include <solver/Z3_C_Solver.h>

#endif /* _AVM_SOLVER_Z3_ */

#endif /* SOLVER_Z3_H_ */
