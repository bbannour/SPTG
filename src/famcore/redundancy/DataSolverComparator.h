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
#ifndef DATASOLVERCOMPARATOR_H_
#define DATASOLVERCOMPARATOR_H_

#include "BaseDataComparator.h"

#include <solver/api/SatSolver.h>


namespace sep
{


class BaseDataSolverComparator : public BaseDataComparator
{

protected:
	/**
	 * ATTRIBUTES
	 */
	SatSolver * mSolver;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseDataSolverComparator(Configuration & aConfiguration)
	: BaseDataComparator( aConfiguration ),
	mSolver( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseDataSolverComparator();


	/**
	 * CONFIGURE
	 */
	virtual bool configure(const WObject * wfParameterObject) override;


	/**
	 * GETTER - SETTER
	 * mSolver
	 */
	inline SatSolver * getSolver()
	{
		return( mSolver );
	}

	inline virtual bool hasVariableComparison() override
	{
		return( (mSolver != nullptr) && mSolver->hasSelectedVariable() );
	}


	/*
	 * COMPARE
	 */
	virtual bool compare(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override;

};



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SOLVER EQUALITY
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class DataSolverEquality : public BaseDataSolverComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	DataSolverEquality(Configuration & aConfiguration)
	: BaseDataSolverComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~DataSolverEquality()
	{
		//!! NOTHING
	}


	/*
	 * COMPARE
	 */
	inline virtual bool compareDATA(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override
	{
		return( getSolver()->isEqualSet(newEC, oldEC) );
	}

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
	{
		return( "== i.e. EQ" );
	}

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// SOLVER INCLUSION
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class DataSolverInclusion : public BaseDataSolverComparator
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	DataSolverInclusion(Configuration & aConfiguration)
	: BaseDataSolverComparator( aConfiguration )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~DataSolverInclusion()
	{
		//!! NOTHING
	}


	/*
	 * COMPARE
	 */
	virtual bool compareDATA(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) override
	{
		return( getSolver()->isSubSet(newEC, oldEC) );
	}

	/**
	 * strComparer
	 */
	inline virtual std::string strComparer() const override
	{
		return( "<= i.e. INCLUSION" );
	}

};


}

#endif /*DATASOLVERCOMPARATOR_H_*/
