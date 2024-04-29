/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef SOLVER_OMEGA_H_
#define SOLVER_OMEGA_H_

#include <solver/api/SolverDef.h>
/*
 * Here because "SolverDef.h" could define this macro
 */
#if defined( _AVM_SOLVER_OMEGA_ )


#include <solver/api/SatSolver.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>

#if defined( _AVM_BUILTIN_NUMERIC_BOOST_ )

// Due to compilation ambiguity between boost::swap & omega::swap
#include <fml/numeric/Float.h>

#endif /* _AVM_BUILTIN_NUMERIC_BOOST_ */

////////////////////////////////////////////////////////////////////////////////
// OMEGA & this old special ASSERT feature
#include "omega.h"
#undef assert
#undef _assert
////////////////////////////////////////////////////////////////////////////////



namespace sep
{

class ExecutionContext;
class ExecutionData;

class WObject;


class OmegaSolver : public SatSolver
{

	AVM_DECLARE_UNCLONABLE_CLASS(OmegaSolver)


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
	VectorOfInstanceOfData mTableOfVariableInstance;
	std::vector< omega::Variable_ID > mTableOfVariableID;

	VectorOfInstanceOfData mTableOfVar4ParamInstance;

	VectorOfInstanceOfData mTableOfParameterInstance;
	std::vector< omega::Variable_ID > mTableOfParameterID;

	omega::F_Declaration * registerExistQuantifier;

	const ExecutionContext * mCacheForNewEC;
	omega::Relation mCacheForNewRelation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	OmegaSolver()
	: SatSolver(),
	registerExistQuantifier( nullptr ),
	mCacheForNewEC( nullptr ),
	mCacheForNewRelation( Relation::Null() )
	{
		//!! NOTHING
		resetParameterTable();
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~OmegaSolver()
	{
		mCacheForNewRelation = Relation::Null();

		resetVariableTable();
	}

	/**
	 * CONFIGURE
	 */
	inline static bool configure(const WObject * wfFilterObject)
	{
		return( true );
	}

	virtual bool configure(
			Configuration & aConfiguration, const WObject * wfFilterObject,
			ListOfPairMachineData & listOfSelectedVariable) override;

	/**
	 * RESET VARIABLE or PARAMETER
	 */
	void resetVariableTable();
	void resetParameterTable();

	/**
	 * SET VARIABLE or PARAMETER
	 */
	virtual void setSelectedVariable(const ExecutionData & apED,
			ListOfPairMachineData & listOfSelectedVariable) override;

	void setSelectedVariable(const ExecutionData & apED);
	void setSelectedVariable(const ExecutionData & apED,
			ListOfInstanceOfData & aLisOfAdditionnalVar);



	/**
	 * PROVER
	 */
	virtual bool isSubSet(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	virtual bool isEqualSet(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

	bool isEmptyIntersection(
			const ExecutionContext & newEC, const ExecutionContext & oldEC);

	virtual SolverDef::SATISFIABILITY_RING isSatisfiable(
			const BF & aCondition) override;

	/**
	 * SOLVER
	 */
	virtual bool solveImpl(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector) override;


	/**
	 * TOOLS
	 */
	bool isSubSet(omega::Relation & Rel1, omega::Relation & Rel2);
	bool isEqualSet(omega::Relation & Rel1, omega::Relation & Rel2);
	bool isEmptyIntersection(omega::Relation & Rel1, omega::Relation & Rel2);

	bool setParameterUple(omega::Relation & aRelation);

	bool toRelation(const ExecutionData & anED, omega::Relation & aRelation);

	omega::Variable_ID getParameterID(InstanceOfData * aParameter);

	void toConjonction(omega::F_And * andNode, const BF & exprForm);

	void toConstraint(omega::Constraint_Handle & constraintNode,
			int coefficient, const BF & exprForm);

};

} /* namespace sep */

#endif /* _AVM_SOLVER_OMEGA_ */


#endif /*SOLVER_OMEGA_H_*/
