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
#include "SatSolver.h"


#include <util/avm_vfs.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionFactory.h>

#include <fml/workflow/WObject.h>


namespace sep
{

class Configuration;


bool SatSolver::configure(
		Configuration & aConfiguration, WObject * wfFilterObject,
		ListOfPairMachineData & listOfSelectedVariable)
{
	mListOfSelectedVariable = listOfSelectedVariable;

	if( mListOfSelectedVariable.empty() )
	{
		AVM_OS_WARNING_ALERT
				<< "Unexpected in SatSolver "
					"an empty selected variable list !!!"
				<< SEND_ALERT;

		return( true );
	}


AVM_IF_DEBUG_FLAG2( CONFIGURING , SOLVING )
	AVM_OS_TRACE << std::endl
			<< "Listes des variables utilisées pour la redondance" << std::endl;

	std::size_t varCount = 0;
	ListOfInstanceOfData::const_iterator itVar;
	ListOfInstanceOfData::const_iterator endVar;

	ListOfPairMachineData::const_iterator itPairMachineData =
			mListOfSelectedVariable.begin();
	ListOfPairMachineData::const_iterator endPairMachineData =
			mListOfSelectedVariable.end();
	for( ; itPairMachineData != endPairMachineData ; ++itPairMachineData )
	{
		AVM_OS_TRACE << "\t" << "Machine:> "
				<< (*itPairMachineData).first().getFullyQualifiedNameID() << std::endl;

		if( (*itPairMachineData).second().nonempty() )
		{
			itVar = (*itPairMachineData).second().begin();
			endVar = (*itPairMachineData).second().end();
			for( ; itVar != endVar ; ++itVar , ++varCount )
			{
				AVM_OS_TRACE << "\t\t" << str_header( *itVar ) << std::endl;
			}
		}
	}

	AVM_OS_TRACE << "Total:> " << varCount << std::endl << std::endl;
AVM_ENDIF_DEBUG_FLAG2( CONFIGURING , SOLVING )


	mLogFolderLocation = VFS::ProjectDebugPath;

	return( true );
}



/**
 * SOLVER
 * an empty << dataVector >> compute by the solver
 * an empty << valuesVector >> compute by the solver
 */
bool SatSolver::solve(const BF & aCondition,
		BFVector & dataVector, BFVector & valuesVector)
{
	BF fullCondition = completeUsingDataTypeConstraint(aCondition, dataVector);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )
	AVM_OS_TRACE << "SatSolver::solve(...) :>" << std::endl
			<< "\tcondition:> " << aCondition.str() << std::endl
			<< "\tfull cond:> " << fullCondition.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , SOLVING )

	if( fullCondition.isEqualTrue() )
	{
		return( true );
	}
	else if( fullCondition.isEqualFalse() )
	{
		return( false );
	}

	return( solveImpl(fullCondition, dataVector, valuesVector) );
}


BF SatSolver::completeUsingDataTypeConstraint(
		const BF & aCondition, BFVector & dataVector) const
{
	BF allCondition = aCondition;
	BF typeConstraint;

	BFVector paramsVector( dataVector );
	ExpressionFactory::collectVariable(aCondition, paramsVector);

	BFVector::raw_iterator< InstanceOfData > itParam = paramsVector.begin();
	BFVector::raw_iterator< InstanceOfData > endParam = paramsVector.end();
	for( ; itParam != endParam ; ++itParam )
	{
		typeConstraint = (itParam)->getTypeSpecifier()->genConstraint( *itParam );

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )
		AVM_OS_TRACE << "completeUsingDataTypeConstraint:> "
				<< str_header( *itParam ) << std::endl
				<< "\tconstraint:> " << typeConstraint.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , SOLVING )

		if( typeConstraint.isEqualFalse() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );
		}
		else if( typeConstraint.isNotEqualTrue() )
		{
			allCondition = ExpressionConstructor::andExpr(
					allCondition, typeConstraint);
		}
	}

	return( allCondition );
}


}
