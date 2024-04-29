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
#ifndef SOLVER_ABSTRACTSOLVER_H_
#define SOLVER_ABSTRACTSOLVER_H_

#include <common/RunnableElement.h>

#include <collection/Typedef.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/runtime/RuntimeID.h>

#include <solver/api/SolverDef.h>


namespace sep
{

class BF;

class Configuration;

class ExecutionContext;

class ExecutionData;

class WObject;


class SatSolver  :  public RunnableElement
{

protected:
	/**
	 * ATTRIBUTES
	 */
	ListOfPairMachineData mListOfSelectedVariable;

	bool mCurrentPathScopeFlag;

	std::string mLogFolderLocation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SatSolver()
	: RunnableElement( nullptr ),
	mListOfSelectedVariable( ),
	mCurrentPathScopeFlag( false ),
	mLogFolderLocation( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~SatSolver()
	{
		//!! NOTHING
	}

	/**
	 * CONFIGURE
	 */
	virtual bool configure(
			Configuration & aConfiguration, const WObject * wfFilterObject,
			ListOfPairMachineData & listOfSelectedVariable);


	/**
	 * INIT / EXIT
	 */
	virtual bool initImpl() override
	{
		//!! NOTHING
		return true;
	}

	virtual bool exitImpl() override
	{
		//!! NOTHING
		return true;
	}

	/**
	 * GETTER - SETTER
	 * mListOfSelectedVariable
	 */
	inline std::string uniqParameterID(const InstanceOfData & aParameter) const
	{
		return aParameter.getUniqNameID();
//		return aParameter.getPortableQualifiedNameID();
//		return aParameter.getUniqQualifiedNameID();

//		return( OSS() << "P_" << aParameter.getMark() << ":"
//					<< aParameter.getPortableQualifiedNameID() );
	}

	inline std::string uniqVariableID(
			const InstanceOfData & aVariable, std::size_t varID)
	{
		return aVariable.getUniqNameID();
//		return aVariable.getPortableQualifiedNameID();
//		return aVariable.getUniqQualifiedNameID();

//		return ( OSS() << "V_" << varID );

//		return( OSS() << "V_" << varID << ":"
//						<< aVariable.getPortableQualifiedNameID() );
	}

	inline std::string uniqVariableID(const Variable & aVariable) const
	{
		return aVariable.getUniqNameID();
	}


	/**
	 * GETTER - SETTER
	 * mListOfSelectedVariable
	 */
	inline ListOfPairMachineData & getSelectedVariable()
	{
		return( mListOfSelectedVariable );
	}

	inline bool hasSelectedVariable()
	{
		return( mListOfSelectedVariable.nonempty() );
	}

	inline virtual void setSelectedVariable(ListOfPairMachineData & aList)
	{
		mListOfSelectedVariable = aList;
	}

	inline virtual void setSelectedVariable(
			const ExecutionData & apED, ListOfPairMachineData & aList)
	{
		mListOfSelectedVariable = aList;
	}


	/**
	 * GETTER - SETTER
	 * mCurrentPathScopeFlag
	 */
	inline bool isCurrentPathScope()
	{
		return( mCurrentPathScopeFlag );
	}

	inline void setCurrentPathScope(bool aCurrentPathScopeFlag)
	{
		mCurrentPathScopeFlag = aCurrentPathScopeFlag;
	}


	/**
	 * GETTER - SETTER
	 * mLogFolderLocation
	 */
	inline std::string getLogFolderLocation()
	{
		return( mLogFolderLocation );
	}

	inline void setLogFolderLocation(const std::string & aLocation)
	{
		mLogFolderLocation = aLocation;
	}



	/**
	 * PROVER
	 */
	virtual bool isSubSet(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) = 0;

	virtual bool isEqualSet(
			const ExecutionContext & newEC,
			const ExecutionContext & oldEC) = 0;

	virtual SolverDef::SATISFIABILITY_RING isSatisfiable(
			const BF & aCondition) = 0;


	/**
	 * SOLVER
	 * an empty << dataVector >> compute by the solver
	 * an empty << valuesVector >> compute by the solver
	 */
	bool solve(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector);

	virtual bool solveImpl(const BF & aCondition,
			BFVector & dataVector, BFVector & valuesVector) = 0;


	BF completeUsingDataTypeConstraint(
			const BF & aCondition, BFVector & dataVector) const;


	/**
	 * SMT2 for DEBUG
	 */
	virtual std::string strTypeSmt2(const ITypeSpecifier & aTypedElement) const;

	virtual bool to_smt(OutStream & os,
			const BF & aCondition, bool enableModelProduction = true) const;

	virtual bool to_smt(OutStream & os,
			const BF & aCondition, BFVector & dataVector) const;

};

}

#endif /*SOLVER_ABSTRACTSOLVER_H_*/
