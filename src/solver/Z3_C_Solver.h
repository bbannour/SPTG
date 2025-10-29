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

#ifndef SOLVER_Z3_C_H_
#define SOLVER_Z3_C_H_
#include <stdbool.h>

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_Z3_C_ )

#include <solver/api/SmtSolver.h>

#include <z3.h>

#include <common/BF.h>

#include <collection/BFContainer.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{

class WObject;


class Z3Solver final :
		public SmtSolver< Z3_symbol , Z3_sort , Z3_ast , true , true >
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
	 */
	Z3_config  CONFIG;

	Z3_context CONTEXT;

	Z3_solver  SOLVER;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Z3Solver(bool forceUniqueID = true);

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
	using SmtSolver::configure;
	static bool configure(const WObject * wfFilterObject);


	/**
	 * PROVER
	 */
	virtual bool isSubSet(const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	virtual bool isEqualSet(const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	virtual SolverDef::SATISFIABILITY_RING isSatisfiable(
			const BF & aCondition) override;


	/**
	 * SOLVER
	 */
	virtual bool solveImpl(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector) override;


	/**
	 * CREATE - DESTROY
	 * ValidityChecker
	 */
	bool createChecker();
	bool destroyChecker() override;
	bool resetTable() override;


	/**
	 * TOOLS
	 */

	Z3_sort getZ3Type(const ITypeSpecifier & bts) const;

	Z3_ast getParameterExpr(const BF & aParameter);

	Z3_ast getBoundParameterExpr(
			const BF & aParameter, ARGS & boundVarConstraints);

	Z3_ast getVariableExpr(InstanceOfData * aVar, std::size_t varID);

	void appendPossitiveAssertion();

	Z3_ast safe_from_baseform(const BF & exprForm);

	Z3_ast from_baseform(const BF & exprForm);

	BF to_baseform(Z3_model model, Z3_ast z3Form);


	/**
	 * Using file API
	 */

	virtual SolverDef::SATISFIABILITY_RING smt_check_sat(const BF & aCondition);

	virtual bool smt_check_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual SolverDef::SATISFIABILITY_RING from_smt_sat(const BF & aCondition);

	virtual bool from_smt_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual bool to_smt(OutStream & os, const BF & aCondition,
			bool enableModelProduction = true,
			bool enableChecksat = true) const override;

	virtual bool to_smtlib(OutStream & os, const BF & aCondition);


	virtual bool to_smt(OutStream & os,
			const BF & exprForm, BFVector & dataVector) const override;

	virtual void dbg_smt(const Z3_solver & z3Solver,
			bool produceModelOption = false) const;

};


} /* namespace sep */

#endif /* _AVM_SOLVER_Z3_C_ */


#endif /* SOLVER_Z3_C_H_ */
