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

#include "AvmGuardPrimitive.h"

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <computer/PathConditionProcessor.h>

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <solver/api/SolverDef.h>
#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 ***************************************************************************
 * execution of a GUARD program
 ***************************************************************************
 */
bool AvmPrimitive_Guard::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "guard :> " << ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )

	if( ENV.mARG->at(0).isEqualTrue()  )
	{
		//!! NO NEED PATH CONDITION UPDATE
		ENV.appendOutput( ENV.mARG->outED );
	}

	else if( ENV.mARG->at(0).isEqualFalse()  )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << GUARD >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str()
			<< " |=> " << ENV.mARG->at(0).str() << EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	else
	{
		if( not PathConditionProcessor::appendPathCondition(
				ENV, ENV.mARG->outED, ENV.mARG->at(0)) )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << GUARD >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "       PC: "
			<< ENV.mARG->outED.getAllPathCondition().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str() << EOL
			<< TAB << "       |=> " << ENV.mARG->at(0).str()
			<< EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a TIMED GUARD program
 ***************************************************************************
 */
bool AvmPrimitive_TimedGuard::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "tguard :> " << ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )

	if( ENV.mARG->at(0).isEqualTrue()  )
	{
		//!! NO NEED PATH CONDITION UPDATE
		ENV.outEDS.append( ENV.mARG->outED );
	}

	else if( ENV.mARG->at(0).isEqualFalse()  )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << GUARD >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str()
			<< " |=> " << ENV.mARG->at(0).str() << EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	else
	{
		if( not PathConditionProcessor::appendPathTimedCondition(
				ENV, ENV.mARG->outED, ENV.mARG->at(0)) )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << TGUARD >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "       PC: "
			<< ENV.mARG->outED.getAllPathCondition().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str() << EOL
			<< TAB << "       |=> " << ENV.mARG->at(0).str()
			<< EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}
	}

	return( true );
}



/**
 ***************************************************************************
 * execution of a EVENT program
 ***************************************************************************
 */
bool AvmPrimitive_Event::run(ExecutionEnvironment & ENV)
{
AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "event :> " << ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )

	if( ENV.mARG->at(0).isEqualTrue()  )
	{
		//!! NO NEED PATH CONDITION UPDATE
		ENV.appendOutput( ENV.mARG->outED );
	}
	else if( ENV.mARG->at(0).isEqualFalse() )
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << EVENT >> : "
			<< ENV.mARG->outED.getRID().strUniqId() << " , "
			<< ENV.inCODE->first().str()  << " |=> "
			<< ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}
	else
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNKNOWN SATISFIABILITY OF << EVENT >> : "
			<< ENV.mARG->outED.getRID().strUniqId() << " , "
			<< ENV.inCODE->first().str()  << " |=> "
			<< ENV.mARG->at(0).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)

		return( false );
	}

	return( true );
}


/**
 ***************************************************************************
 * execution of a CHECK_SAT program
 ***************************************************************************
 */
bool AvmPrimitive_CheckSat::run(ExecutionEnvironment & ENV)
{
	if( ENV.mARG->at(0).isBuiltinString() )
	{
		std::string theSolver = ENV.mARG->at(0).toBuiltinString();

AVM_IF_DEBUG_FLAG( STATEMENT_TEST_DECISION )
	AVM_OS_TRACE << "checkSat< " << theSolver << " > "
			<< ENV.mARG->at(1).str() << std::endl;
AVM_ENDIF_DEBUG_FLAG( STATEMENT_TEST_DECISION )

		if( ENV.mARG->at(1).isEqualTrue()  )
		{
			//!! NO NEED PATH CONDITION UPDATE
			ENV.appendOutput( ENV.mARG->outED );
		}

		else if( ENV.mARG->at(1).isEqualFalse()  )
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << CHECK#SAT >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str()
			<< " |=> " << ENV.mARG->at(0).str()
			<< EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}

		else if( SolverFactory::isWeakSatisfiable(SolverDef::toSolver(
				theSolver, SolverDef::DEFAULT_SOLVER_KIND), ENV.mARG->at(1)) )
		{
			//!! NO NEED PATH CONDITION UPDATE
			ENV.appendOutput( ENV.mARG->outED );
		}
		else
		{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << CHECK#SAT >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "       PC: "
			<< ENV.mARG->outED.getAllPathCondition().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str() << EOL
			<< TAB << "       |=> " << ENV.mARG->at(0).str()
			<< EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
		}

		return( true );
	}


	else if( SolverFactory::isWeakSatisfiable(ENV.mARG->at(0)) )
	{
		//!! NO NEED PATH CONDITION UPDATE
		ENV.appendOutput( ENV.mARG->outED );
	}
	else
	{
AVM_IF_DEBUG_FLAG( STATEMENT)
	AVM_OS_TRACE << "THROW UNSATISFIED << CHECK#SAT >> :> ctx: "
			<< ENV.mARG->outED.getRID().str() << EOL
			<< TAB << "       PC: "
			<< ENV.mARG->outED.getAllPathCondition().str() << EOL
			<< TAB << "condition: " << ENV.inCODE->str() << EOL
			<< TAB << "       |=> " << ENV.mARG->at(0).str()
			<< EOL_FLUSH;
AVM_ENDIF_DEBUG_FLAG( STATEMENT)
	}

	return( true );
}


}
