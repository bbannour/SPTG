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
#include "DataSolverComparator.h"

#include <fam/redundancy/RedundancyFilter.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * DESTRUCTOR
 */
BaseDataSolverComparator::~BaseDataSolverComparator()
{
	SolverFactory::destroy( mSolver );
}


/**
 ***************************************************************************
prototype filter::redundancy as avm::core.filter.REDUNDANCY is
section PROPERTY
	@predicate = 'INCLUSION';  // ( <=  | INC | INCLUSION )
	                              ( ==  | EQ  | EQUALITY )
	                              ( =a= | AEQ | ALPHA_EQUIV)
	                              ( =s= | SEQ | SYNTAXIC_EQUALITY)
	                              ( =t= | TEQ | TRIVIALLY_EQUALITY)
	                              NONE

	@solver = 'OMEGA';         // OMEGA | CVC3

	@path_scope = 'ALL';       // ALL execution graph path | CURRENT execution graph path

	@data_scope = 'ALL';       // ALL data ; or DETAILS section
	                           // DETAILS | DETAILS< exclude > some data,
endsection PROPERTY

section HEURISTIC
	@communication = false;

	@variable = true;
	@path_condition = false;
endsection HEURISTIC

section DETAILS
	@model = ufi;

	@instance = ufi;

	@variable = ufi;
endsection DETAILS
endprototype
***************************************************************************
*/


/**
 * CONFIGURE
 */
bool BaseDataSolverComparator::configure(WObject * wfParameterObject)
{
	if( not BaseDataComparator::configure(wfParameterObject) )
	{
		return( false );
	}

	WObject * thePROPERTY =
			RedundancyFilter::AUTO_REGISTER_TOOL.isTypeID( * wfParameterObject )
			? Query::getRegexWSequence(wfParameterObject,
					OR_WID2("property", "PROPERTY"), wfParameterObject)
			: Query::getRegexWSequence(wfParameterObject,
					OR_WID2("redundancy" , "REDUNDANCY"), wfParameterObject);

	std::string solverID = Query::getWPropertyString(thePROPERTY, "solver",
			SolverDef::strSolver(SolverDef::SOLVER_OMEGA_KIND));

	AVM_OS_ASSERT_FATAL_ERROR_EXIT( SolverDef::isAvailableSolver(
			SolverDef::toSolver(solverID, SolverDef::SOLVER_UNDEFINED_KIND)) )
			<< "Redundancy: Unknown solver << " << solverID
			<< " >> as parameter (trying to use the default OMEGA solver)!!!"
			<< SEND_ALERT;

	SolverDef::SOLVER_KIND solverKing =
			SolverDef::toSolver(solverID, SolverDef::SOLVER_OMEGA_KIND);

	if( not SolverDef::isAvailableSolver( solverKing ) )
	{
		AVM_OS_ERROR_ALERT<< "Redundancy: Unknown solver << "
				<< solverID << " >> !!!"
				<< SEND_EXIT;

		mSolver = NULL;

		return( false );
	}

	mSolver = SolverFactory::newSolver4CheckSatisfiability( solverKing );

	if( mSolver != NULL )
	{
		mSolver->setCurrentPathScope( isCurrentPathScope() );

		return( mSolver->configure(mConfiguration,
				wfParameterObject, getSelectedPresburgerVariable()) );
	}
	else
	{
		AVM_OS_ERROR_ALERT << "Unexpected REDUNDANCY filter << @solver = "
				<< solverID << "; >> !!!" << std::endl
				<< "NB. << @solver = { 'OMEGA' | 'CVC4' }; >> !!!"
				<< SEND_ALERT;

		return( false );
	}

	return( true );
}



/*
 * COMPARE
 */
bool BaseDataSolverComparator::compare(
		const ExecutionContext & newEC, const ExecutionContext & oldEC)
{
	if( mMachineCount != newEC.refExecutionData().getTableOfRuntime().size() )
	{
		mMachineCount = newEC.refExecutionData().getTableOfRuntime().size();

		computeAllMachineData( newEC.refExecutionData() );

		getSolver()->setSelectedVariable(
				mConfiguration.getMainExecutionData(),
				getSelectedPresburgerVariable() );
	}

	if( mCurrentPathScopeFlag )
	{
		refreshCurrentVariables(getCurrentPresburgerVariable(),
				getSelectedPresburgerVariable(),
				newEC.refExecutionData(), oldEC.refExecutionData());

		getSolver()->setSelectedVariable(newEC.refExecutionData(),
				getCurrentPresburgerVariable());
	}

	if( compareTEQ(newEC, oldEC) )
	{
		return( true );
	}
	else if( mUseCommunication || mUseVariable )
	{
		return( (mUseCommunication ? compareIO(newEC, oldEC) : true)
				&& (mUseVariable ? compareDATA(newEC, oldEC) : true) );
	}

	return( true );
}



}
