/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmBaseConcurrencyPrimitive.h"

#include <computer/PathConditionProcessor.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionSimplifier.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/*
 ***************************************************************************
 ***************************************************************************
 * EVAL EXCLUSIVE
 ***************************************************************************
 ***************************************************************************
 */


// Compute EVAL where NOT OTHER
bool AvmBaseConcurrencyPrimitive::evalExclusive(APExecutionData & anInputED,
		APExecutionData & evalED, APExecutionData & otherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	BF theNodeCondition = otherED->getNodeCondition();

	if( theNodeCondition.isEqualTrue() )
	{
		return( false );
	}
	else if( theNodeCondition.isEqualFalse() )
	{
		listOfOutputED.append( evalED );

		return( true );
	}
	else
	{
		theNodeCondition = ExpressionConstructor::notExpr(theNodeCondition);

		return( PathConditionProcessor::appendPathCondition(
				evalED, theNodeCondition, listOfOutputED) );
	}
}


// Compute EVAL where NOT OTHERS
bool AvmBaseConcurrencyPrimitive::evalExclusive(APExecutionData & anInputED,
		APExecutionData & evalED, ListOfAPExecutionData & listOfOtherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	if( listOfOtherED.empty() )
	{
		listOfOutputED.append( evalED );

		return( true );
	}

	else if( listOfOtherED.singleton() )
	{
		return( evalExclusive(anInputED, evalED,
				listOfOtherED.last(), listOfOutputED) );
	}

	else
	{
		BFCode theNodeConditions(OperatorManager::OPERATOR_OR);

		ListOfAPExecutionData::iterator it = listOfOtherED.begin();
		ListOfAPExecutionData::iterator itEnd = listOfOtherED.end();
		for( ; it != itEnd ; ++it )
		{
			theNodeConditions->append( (*it)->getNodeCondition() );
		}

		BF theNodeCondition =
				ExpressionSimplifier::simplif( theNodeConditions );


		if( theNodeCondition.isEqualTrue() )
		{
			return( false );
		}
		else if( theNodeCondition.isEqualFalse() )
		{
			listOfOutputED.append( evalED );

			return( true );
		}
		else
		{
			theNodeCondition =
					ExpressionConstructor::notExpr(theNodeCondition);

			return( PathConditionProcessor::appendPathCondition(
					evalED, theNodeCondition, listOfOutputED) );
		}
	}
}


bool AvmBaseConcurrencyPrimitive::evalExclusive(APExecutionData & anInputED,
		ListOfAPExecutionData & oneListOfED, APExecutionData & otherED,
		CollectionOfAPExecutionData & listOfOutputED)
{
	ListOfAPExecutionData::iterator itOne;
	ListOfAPExecutionData::iterator endOne = oneListOfED.end();

	// Compute OTHER where NOT ONE
	for( itOne = oneListOfED.begin() ; itOne != endOne ; ++itOne )
	{
		if( not evalExclusive(anInputED, *itOne, otherED, listOfOutputED) )
		{
			return( false );
		}
	}

	return( true );
}



}
