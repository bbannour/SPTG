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

#include "AvmSchedulingPrimitive.h"

#include <computer/ExecutionEnvironment.h>
#include <computer/PathConditionProcessor.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstant.h>

#include <fml/operator/OperatorManager.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an EXCLUSIVE program
 ***************************************************************************
 */
bool AvmPrimitive_Exclusive::run(ExecutionEnvironment & ENV)
{
	ENV.inED->setEnabledLocalNodeCondition( true );

	ListOfAPExecutionData oneListOfED;
	ListOfAPExecutionData resultListOfED;

	AvmCode::const_iterator it = ENV.inCODE->begin();
	AvmCode::const_iterator itEnd = ENV.inCODE->end();

	// Initialisation du process
	ExecutionEnvironment tmpENV(ENV, *it);
	if( not tmpENV.run() )
	{
		return( false );
	}
	oneListOfED.splice( tmpENV.outEDS );

	// Recurrence
	for( ++it ; it != itEnd ; ++it )
	{
		if( not tmpENV.run(*it) )
		{
			return( false );
		}

		// COMPUTE STRONG FUSION
		if( oneListOfED.empty() )
		{
			resultListOfED.splice( tmpENV.outEDS );
		}
		else if( tmpENV.outEDS.empty() )
		{
			resultListOfED.splice( oneListOfED );
		}

		else
		{
			ListOfAPExecutionData::iterator itOther = tmpENV.outEDS.begin();
			ListOfAPExecutionData::iterator endOther = tmpENV.outEDS.end();
			for( ; itOther != endOther ; ++itOther )
			{
				// Compute OTHER where NOT ONE
				if( not evalExclusive(ENV.inED,
						oneListOfED, (*itOther), resultListOfED) )
				{
					//return( false );
				}

				// Compute ONE where NOT OTHERS
				if( not evalExclusive(ENV.inED,
						(*itOther), oneListOfED, resultListOfED) )
				{
					//return( false );
				}
			}

			oneListOfED.clear();
			resultListOfED.makeUnique();
		}

		while( resultListOfED.nonempty() )
		{
			resultListOfED.last()->setEnabledLocalNodeCondition( false );

			oneListOfED.append( resultListOfED.pop_last() );
		}
	}

	ENV.inED->setEnabledLocalNodeCondition( false );

	ENV.outEDS.splice( oneListOfED );

	ENV.spliceNotOutput( tmpENV );

	return( true );
}


/**
 ***************************************************************************
 * execution of an NONDETERMINISM program
 ***************************************************************************
 */
bool AvmPrimitive_Nondeterminism::run(ExecutionEnvironment & ENV)
{
	AvmCode::const_iterator endIt = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != endIt ; ++it )
	{
		ENV.run( *it );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a PRIOR program
 ***************************************************************************
 */
bool AvmPrimitive_Prior::run(ExecutionEnvironment & ENV)
{
	APExecutionData tmpED;

	BF aPathCondition;
	BF aPriorityCondition = ExpressionConstant::BOOLEAN_TRUE;

	BFCode theNodeCondition( OperatorManager::OPERATOR_OR );

	BF saveParamsRF = ENV.inED->bfParametersRuntimeForm();

	BF bfUpdateParamsRF = saveParamsRF;
	bfUpdateParamsRF.makeWritable();
	ParametersRuntimeForm * updateParamsRF =
			bfUpdateParamsRF.to_ptr< ParametersRuntimeForm >();

	// Recurrence
	AvmCode::const_iterator itEnd = ENV.inCODE->end();
	for( AvmCode::const_iterator it = ENV.inCODE->begin() ; it != itEnd ; ++it )
	{
		ENV.inED->assignParametersRuntimeForm( bfUpdateParamsRF );

		ExecutionEnvironment tmpENV(ENV, *it);
		tmpENV.inED->setEnabledLocalNodeCondition( true );

		tmpENV.run();

		if( tmpENV.outEDS.nonempty() || tmpENV.exitEDS.nonempty() )
		{
			while( tmpENV.outEDS.nonempty() )
			{
				tmpENV.outEDS.pop_last_to( tmpED );

				if( aPriorityCondition.isEqualTrue() )
				{
					aPathCondition = tmpED->getPathCondition();
				}
				else if( tmpED->getPathCondition().isEqualTrue() )
				{
					aPathCondition = aPriorityCondition;
				}
				else
				{
					aPathCondition = ExpressionConstructor::andExpr(
							aPriorityCondition, tmpED->getPathCondition());

					if( not PathConditionProcessor::isWeakSatisfiable(
							aPathCondition) )
					{
						aPathCondition = ExpressionConstant::BOOLEAN_FALSE;

AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "PATH CONDITION : "
			<< tmpED->getPathCondition().str() << std::endl
			<< "PRIORITY CONDITION : " << aPriorityCondition.str() << std::endl
			<< "FIREABLE CONDITION : " << aPathCondition.str()     << std::endl
			<< "THROW UNSATISFIED << PRIOR CONDITION >> : "
			<< tmpED->mRID.strUniqId() << " |=> " << (*it).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
					}
				}

				if( aPathCondition.isNotEqualFalse() )
				{
					if( tmpED->getAllNodeCondition().isNotEqualTrue() )
					{
						theNodeCondition->append( tmpED->getAllNodeCondition() );

						updateParamsRF->update( tmpED->getAllNodeCondition() );
					}

					tmpED->setPathCondition( aPathCondition );
					tmpED->setEnabledLocalNodeCondition( false );

					ENV.outEDS.append( tmpED );
				}
			}

			while( tmpENV.exitEDS.nonempty() )
			{
				tmpENV.exitEDS.pop_last_to( tmpED );

				if( aPriorityCondition.isEqualTrue() )
				{
					aPathCondition = tmpED->getPathCondition();
				}
				else if( tmpED->getPathCondition().isEqualTrue() )
				{
					aPathCondition = aPriorityCondition;
				}
				else
				{
					aPathCondition = ExpressionConstructor::andExpr(
							aPriorityCondition, tmpED->getPathCondition());

					if( not PathConditionProcessor::isWeakSatisfiable(
							aPathCondition) )
					{
						aPathCondition = ExpressionConstant::BOOLEAN_FALSE;

AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "PATH CONDITION : "
			<< tmpED->getPathCondition().str() << std::endl
			<< "PRIORITY CONDITION : " << aPriorityCondition.str() << std::endl
			<< "FIREABLE CONDITION : " << aPathCondition.str()     << std::endl
			<< "THROW UNSATISFIED << PRIOR CONDITION >> : "
			<< tmpED->mRID.strUniqId() << " |=> " << (*it).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
					}
				}

				if( aPathCondition.isNotEqualFalse() )
				{
					if( tmpED->getAllNodeCondition().isNotEqualTrue() )
					{
						theNodeCondition->append( tmpED->getAllNodeCondition() );

						updateParamsRF->update( tmpED->getAllNodeCondition() );
					}

					tmpED->setPathCondition( aPathCondition );
					tmpED->setEnabledLocalNodeCondition( false );

					ENV.exitEDS.append( tmpED );
				}
			}


			if( theNodeCondition->empty() )
			{
				//aPriorityCondition = ExpressionConstant::BOOLEAN_FALSE; // <=> not true
				break;
			}

			else if( theNodeCondition->populated() )
			{
				aPriorityCondition = ExpressionConstructor::notExpr(
						theNodeCondition );
			}
			else
			{
				aPriorityCondition = ExpressionConstructor::notExpr(
						theNodeCondition->pop_last() );
			}

			if( not PathConditionProcessor::isWeakSatisfiable(
					aPriorityCondition) )
			{
				break;
			}

AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "PRIORITY CONDITION : " << aPriorityCondition.str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
		}

		ENV.spliceNotOutput( tmpENV );
	}

	ENV.inED->assignParametersRuntimeForm( saveParamsRF );


	return( true );
}


/**
 ***************************************************************************
 * execution of an AND#THEN program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleAndThen::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, BF::REF_NULL);

	tmpENV.outEDS.append(tmpENV.inED);

	AvmCode::const_iterator itArg = ENV.inCODE->begin();
	AvmCode::const_iterator endArg = ENV.inCODE->end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( tmpENV.runFromOutputs( (*itArg).bfCode() ) )
		{
			if( tmpENV.outEDS.empty()  && tmpENV.exitEDS.empty() &&
				tmpENV.syncEDS.empty() && tmpENV.irqEDS.empty() )
			{
				break;
			}
			else
			{
				// THEN case
			}
		}
	}

	ENV.spliceOutput( tmpENV );

	return( true );
}


/**
 ***************************************************************************
 * execution of an OR#ELSE program
 ***************************************************************************
 */
bool AvmPrimitive_ScheduleOrElse::run(ExecutionEnvironment & ENV)
{
	ExecutionEnvironment tmpENV(ENV, BF::REF_NULL);

	AvmCode::const_iterator itArg = ENV.inCODE->begin();
	AvmCode::const_iterator endArg = ENV.inCODE->end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( tmpENV.run( (*itArg).bfCode() ) )
		{
			if( tmpENV.outEDS.nonempty()  || tmpENV.exitEDS.nonempty() ||
				tmpENV.syncEDS.nonempty() || tmpENV.irqEDS.nonempty() )
			{
				ENV.spliceOutput( tmpENV );

				break;
			}
			else
			{
				// ELSE case
			}
		}

		ENV.spliceOutput( tmpENV );
	}

	return( true );
}




}
