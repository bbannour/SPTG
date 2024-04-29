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

#ifndef SOLVER_CVC5_H_
#define SOLVER_CVC5_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_CVC5_ )


#include <solver/api/SmtSolver.h>

#include <cvc5/cvc5.h>

#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{


class WObject;

class ExecutionContext;
class ExecutionData;

class TypeSpecifier;


class CVC5Solver :
		public SmtSolver< cvc5::Term , cvc5::Sort , cvc5::Term , false , true >

{

	AVM_DECLARE_UNCLONABLE_CLASS(CVC5Solver)

public:
	/*
	 ***************************************************************************
	 * ID
	 ***************************************************************************
	 */
	static std::string ID;

	static std::string DESCRIPTION;

	static std::uint64_t SOLVER_SESSION_ID;

	static 	cvc5::Term CVC5_EXPR_NULL;
	static 	cvc5::Sort CVC5_TYPE_NULL;



protected:
	/**
	 * ATTRIBUTES
	 **/
	std::string mParamPrefix;

//	cvc5::ExprManager mExprManager;
	cvc5::Solver  mSmtEngine;


public:
	/**
	* CONSTRUCTOR
	* Default
	*/
	CVC5Solver(bool produce_models_flag = false);

	/**
	* DESTRUCTOR
	*/
	virtual ~CVC5Solver();

	/**
	 * CONFIGURE
	 */
	static bool configure(const WObject * wfFilterObject);


	/**
	 * PROVER
	 */
	virtual bool isSubSet(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	virtual bool isEqualSet(
			const ExecutionContext & newEC,
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
	virtual bool destroyChecker() override;
	virtual bool resetTable() override;

	/**
	 * TOOLS
	 */
	void edToExpr(const ExecutionData & newED, cvc5::Term & newFormula,
			const ExecutionData & oldED, cvc5::Term & oldFormula);

	void edToExprWithVarEquality(const ExecutionData & newED,
			cvc5::Term & newFormula, const ExecutionData & oldED,
			cvc5::Term & oldFormula, cvc5::Term & equFormula);

	cvc5::Term  edToExpr(const ExecutionData & anED);

	bool appendPossitiveAssertion();

	cvc5::Term safe_from_baseform(const BF & exprForm);

	cvc5::Term from_baseform(const BF & exprForm);

	cvc5::Term & getParameterExpr(const BF & aParameter);
	cvc5::Term & getVariableExpr(InstanceOfData * aVar,
			cvc5::Sort varType, avm_offset_t varID);

	cvc5::Term & getBoundParameterExpr(
			const BF & aParameter, ARGS & boundVarConstraints);


	virtual void dbg_smt(const cvc5::Term & aFormula, bool produceModelOption = false) const;

};


} /* namespace sep */

#endif /* _AVM_SOLVER_CVC5_ */


#endif /* SOLVER_CVC5_H_ */

