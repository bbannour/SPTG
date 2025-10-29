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

#include "AvmItePrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <computer/PathConditionProcessor.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of an IF program
 ***************************************************************************
 */
bool AvmPrimitive_If::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).isEqualTrue() )
	{
		// THEN STATEMENT
		ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, ENV.mARG->at(1).bfCode());
		if( tmpENV.run() )
		{
			ENV.spliceOutput( tmpENV );
		}
		else
		{
			return( false );
		}
	}
	else if( ENV.mARG->at(0).isEqualFalse() )
	{
		ENV.appendOutput( ENV.mARG->outED );
//		ENV.xappendOutED( ENV.mARG->outED , aProgram );
	}

	else
	{
		// THEN STATEMENT
		ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, ENV.mARG->at(0));
		if( PathConditionProcessor::appendPathCondition(tmpENV) )
		{
			if( tmpENV.runFromOutputs(ENV.mARG->at(1).bfCode()) )
			{
				ENV.spliceOutput( tmpENV );
			}
			else
			{
				return( false );
			}

			////////////////////////////////////////////////////////////////
			// CASE ELSE { NOP }
			BF elseCond = ExpressionConstructor::notExpr(ENV.mARG->at(0));
			if( not PathConditionProcessor::appendPathCondition(
					ENV, ENV.mARG->outED, elseCond) )
			{
				// NOTHING
			}
		}
		else
		{
			////////////////////////////////////////////////////////////////
			// CASE ELSE { NOP }
			ENV.appendOutput( ENV.inED );
		}
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of an IFE program
 ***************************************************************************
 */
bool AvmPrimitive_Ife::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).isEqualTrue() )
	{
		// THEN STATEMENT
		ExecutionEnvironment tmpENV(ENV, ENV.mARG->outED, ENV.mARG->at(1).bfCode());
		if( tmpENV.run() )
		{
			ENV.spliceOutput( tmpENV );
		}
		else
		{
			return( false );
		}
	}
	else if( ENV.mARG->at(0).isEqualFalse() )
	{
		// ELSE STATEMENT
		ExecutionEnvironment tmpENV(ENV, ENV.mARG->at(2).bfCode());
		if( tmpENV.run() )
		{
			ENV.spliceOutput( tmpENV );
		}
		else
		{
			return( false );
		}
	}

	else
	{
		// THEN STATEMENT
		ExecutionEnvironment thenENV(ENV, ENV.mARG->outED, ENV.mARG->at(0));
		if( PathConditionProcessor::appendPathCondition(thenENV) )
		{
			if( thenENV.runFromOutputs(ENV.mARG->at(1).bfCode()) )
			{
				ENV.spliceOutput( thenENV );
			}
			else
			{
				return( false );
			}
		}

		////////////////////////////////////////////////////////////////
		// ELSE STATEMENT
		BF elseCond = ExpressionConstructor::notExpr(ENV.mARG->at(0));
		ExecutionEnvironment elseENV(ENV, ENV.mARG->outED, elseCond);
		if( PathConditionProcessor::appendPathCondition(elseENV) )
		{
			if( elseENV.runFromOutputs(ENV.mARG->at(2).bfCode()) )
			{
				ENV.spliceOutput( elseENV );
			}
			else
			{
				return( false );
			}
		}
	}

	return( true );
}




}
