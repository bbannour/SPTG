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

#ifndef SOLVER_YICES2_H_
#define SOLVER_YICES2_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_YICES_V2_ )


#include <solver/api/SmtSolver.h>

#include <yices_types.h>

#include <common/BF.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{


class Yices2Solver :
		public SmtSolver< term_t , term_t , term_t , true , true >
{

	AVM_DECLARE_UNCLONABLE_CLASS(Yices2Solver)


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
	ctx_config_t * CFG;

	context_t * CTX;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Yices2Solver();


	/**
	 * DESTRUCTOR
	 */
	virtual ~Yices2Solver();


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

	type_t getYicesType(const BaseTypeSpecifier & bts);

	term_t getParameterExpr(const BF & bfParameter);
	term_t getVariableExpr(InstanceOfData * aVar, std::size_t varID);

	term_t getBoundParameterExpr(const BF & bfParameter);


	term_t safe_from_baseform(const BF & exprForm);

	term_t from_baseform(const BF & exprForm);

	BF to_baseform(model_t * model, term_t param, const BaseTypeSpecifier & bts);


	/**
	 * Using file API
	 */

	virtual SolverDef::SATISFIABILITY_RING smt_check_sat(
			const BF & aCondition, BFVector & paramVector);

	virtual bool smt_check_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual SolverDef::SATISFIABILITY_RING from_smt_sat(const BF & aCondition);

	virtual bool from_smt_model(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);


	virtual std::string strTypeSmt2(const ITypeSpecifier & aTypedElement) const override;

	virtual bool to_smt(OutStream & os, const BF & aCondition,
			bool enableModelProduction = true) const override;

	virtual bool to_smt(OutStream & os,
			const BF & aCondition, BFVector & dataVector) const override;


	virtual void dbg_smt(term_t aTerm, model_t * aModel,
			BFVector & paramVector, bool produceModelOption = false) const;

};


} /* namespace sep */

#endif /* _AVM_SOLVER_YICES_V2_ */


#endif /* SOLVER_YICES2_H_ */
