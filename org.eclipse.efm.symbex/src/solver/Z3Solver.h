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

// TODO for << z3 cpp interface >>
//#define _AVM_SOLVER_Z3_CPP_


#ifndef SOLVER_Z3_H_
#define SOLVER_Z3_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_Z3_ )


#include <solver/api/SmtSolver.h>

#include <z3/z3++.h>


#include <common/BF.h>

#include <collection/BFContainer.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{

class WObject;


#if defined( _AVM_SOLVER_Z3_CPP_ )


class Z3Solver :
		public SmtSolver< z3::symbol , z3::sort , z3::expr , true , false >
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

	static avm_uint64_t SOLVER_SESSION_ID;


protected:
	/**
	 * ATTRIBUTES
	 **/
	z3::config * CFG;

	z3::context * CTX;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Z3Solver()
	: base_this_type( ),
	CFG( NULL ),
	CTX( NULL )
	{
		//!!! NOTHING
	}


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
	bool createChecker(z3::config & cfg, z3::context & ctx);
	bool destroyChecker();
	bool resetTable();


	/**
	 * TOOLS
	 */

	z3::sort getZ3Type(BaseTypeSpecifier * bts);

	z3::expr getParameterExpr(const BF & aParameter);
	z3::expr getVariableExpr(InstanceOfData * aVar, std::size_t varID);


	z3::expr safe_from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

	z3::expr from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

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

	virtual void to_smt(OutStream & os,
			const BF & exprForm, BFVector & dataVector) const;

};


#else /* NOT _AVM_SOLVER_Z3_CPP_  ==> _AVM_SOLVER_Z3_C << default >> */


class Z3Solver :
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

	static avm_uint64_t SOLVER_SESSION_ID;


protected:
	/**
	 * ATTRIBUTES
	 */
	Z3_config CFG;

	Z3_context CTX;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Z3Solver()
	: base_this_type(NULL, NULL),
	CFG( NULL ),
	CTX( NULL )
	{
		//!!! NOTHING
	}


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

	Z3_sort getZ3Type(BaseTypeSpecifier * bts);

	Z3_ast getParameterExpr(const BF & aParameter);
	Z3_ast getVariableExpr(InstanceOfData * aVar, std::size_t varID);


	Z3_ast safe_from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

	Z3_ast from_baseform(const BF & exprForm,
			BaseTypeSpecifier * typeSpecifier = NULL);

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

	virtual void to_smt(OutStream & os,
			const BF & exprForm, BFVector & dataVector) const;

};


#endif /* _AVM_SOLVER_Z3_CPP_ */


} /* namespace sep */

#endif /* _AVM_SOLVER_Z3_ */


#endif /* SOLVER_Z3_H_ */
