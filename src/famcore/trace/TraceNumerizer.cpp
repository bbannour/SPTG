/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceNumerizer.h"

#include "TraceManager.h"

#include <computer/EvaluationEnvironment.h>

#include <solver/api/SolverFactory.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 section PROPERTY
  ...
  // 'OMEGA' | 'CVC4' | 'Z3' | 'YICES'
  @solver = 'CVC4';

  @numerizer = 'SOLVER';  // SOLVER | NONE | NEWFRESH
  ...
 endsection PROPERTY

 ...

endprototype
*/

bool TraceNumerizer::configure(const WObject * wfParameterObject)
{
	const WObject * thePROPERTY = Query::getRegexWSequence(wfParameterObject,
			OR_WID2("property", "PROPERTY"), wfParameterObject);

	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string strAttribrute = Query::getWPropertyString(
				thePROPERTY, "numerizer", "SOLVER");
		if( strAttribrute == "SOLVER" )
		{
			mNumerizerOperator = AVM_OPCODE_CHECK_SAT;
		}
		else if( strAttribrute == "NEWFRESH" )
		{
			mNumerizerOperator = AVM_OPCODE_ASSIGN_NEWFRESH;
		}
		else //if( strAttribrute == "NONE" )
		{
			mNumerizerOperator = AVM_OPCODE_NOP;
		}

		strAttribrute = Query::getWPropertyString(thePROPERTY, "solver", "");

		mSolverKind = SolverDef::toSolver(
				strAttribrute, SolverDef::DEFAULT_SOLVER_KIND);
	}
	else
	{
		mNumerizerOperator = AVM_OPCODE_CHECK_SAT;

		mSolverKind = SolverDef::DEFAULT_SOLVER_KIND;
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// NUMERIZE API
////////////////////////////////////////////////////////////////////////////////

void TraceNumerizer::numerize(TraceManager & aTraceManager)
{
	switch( mNumerizerOperator ) {
		case AVM_OPCODE_CHECK_SAT:
		{
			numerizeSolver( aTraceManager );

			break;
		}
		case AVM_OPCODE_ASSIGN_NEWFRESH:
		{
			numerizeNewfresh( aTraceManager );

			break;
		}
		case AVM_OPCODE_NOP:
		{
			numerizeNothing( aTraceManager );

			break;
		}

		default:
		{
			numerizeSolver( aTraceManager );

			break;
		}
	}
}


void TraceNumerizer::numerizeSolver(TraceManager & aTraceManager)
{
	TraceManager::iterator it = aTraceManager.begin();
	TraceManager::iterator endIt = aTraceManager.end();
	while( it != endIt )
	{
		aTraceElement = (*it);

		aTraceEC = aTraceElement->mEC;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
	AVM_OS_TRACE << "Avant la résolution par le solveur..." << EOL_FLUSH;
	//	aTraceEC->getExecutionData().toStreamData(AVM_OS_TRACE);
	aTraceEC->getExecutionData().getParametersRuntimeForm().
			toStreamData(aTraceEC->getExecutionData(), AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )

		modelED = SolverFactory::solve(mSolverKind, ENV, (* aTraceEC),
				aTraceEC->getExecutionData().getAllPathCondition() );

		if( modelED.invalid() )
		{
AVM_IF_DEBUG_ENABLED
	AVM_OS_WARN << "Error checking model: trace < "
			<< aTraceElement->tid << " > for leaf context "
			<< aTraceEC->str_min()  << std::endl << " |= "
			<< aTraceEC->getExecutionData().getAllPathCondition().wrapStr()
			<< std::endl;
AVM_ENDIF_DEBUG_ENABLED

			// iterator incrementation
			it = aTraceManager.erase( it );

			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
	AVM_OS_TRACE << "Après la résolution par le solveur..." << EOL_FLUSH;
//	modelED.toStreamData(AVM_OS_TRACE);
	modelED.getParametersRuntimeForm().toStreamData(modelED, AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )

		SolverFactory::setModel(ENV, modelED);

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
	AVM_OS_TRACE << "Après la génération du modèle par le solveur..." << EOL_FLUSH;
//	modelED.toStreamData(AVM_OS_TRACE);
	modelED.getParametersRuntimeForm().toStreamData(modelED, AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )

		numerize( *aTraceElement );

		SolverFactory::resetModel(modelED);

		// iterator incrementation
		++it;
	}
}


void TraceNumerizer::numerizeNewfresh(TraceManager & aTraceManager)
{
	TraceManager::const_iterator it = aTraceManager.begin();
	TraceManager::const_iterator endIt = aTraceManager.end();
	for( ; it != endIt ; ++it )
	{
		aTraceElement = (*it);

		aTraceEC = aTraceElement->mEC;

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
	AVM_OS_TRACE << "Avant la résolution par le solveur..." << EOL_FLUSH;
	//	aTraceEC->getExecutionData().toStreamData(AVM_OS_TRACE);
	aTraceEC->getExecutionData().getParametersRuntimeForm().toStreamData(
			aTraceEC->getExecutionData(), AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )

		modelED = SolverFactory::solveNewfresh(mSolverKind, ENV, (* aTraceEC),
				aTraceEC->getExecutionData().getAllPathCondition() );

		if( modelED.invalid() )
		{
AVM_IF_DEBUG_ENABLED
			AVM_OS_WARN << "Error checking model for :> "
					<< aTraceEC->str_min() << std::endl << " |= "
					<< aTraceEC->getExecutionData().getAllPathCondition().str()
					<< std::endl;
AVM_ENDIF_DEBUG_ENABLED

			continue;
		}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )
	AVM_OS_TRACE << "Après la résolution / génération par le solveur..." << EOL_FLUSH;
//	modelED.toStreamData(AVM_OS_TRACE);
	modelED.getParametersRuntimeForm().toStreamData(modelED, AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , SOLVING , TRACE )

		numerize( *aTraceElement );

		SolverFactory::resetModel(modelED);
	}
}

void TraceNumerizer::numerizeNothing(TraceManager & aTraceManager)
{
	//!! NOTHING
}


void TraceNumerizer::numerize(TraceSequence & aTraceElt)
{
	for( auto & itPoint : aTraceElt.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			numerize( itPoint.to< TracePoint >() );
		}

		else if( itPoint.is< TraceSequence >() )
		{
			numerize( itPoint.to< TraceSequence >() );
		}
	}
}

void TraceNumerizer::numerize(TracePoint & aTracePoint)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , SOLVING , TRACE )
	AVM_OS_TRACE << "TraceNumerizer::numerize(TracePoint):> " << std::endl;
	aTracePoint.toStream(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , SOLVING , TRACE )

	if( aTracePoint.value.invalid() )
	{
		//!! NOTING
	}
	else if( aTracePoint.value.is< ArrayBF >() )
	{
		ArrayBF & array = aTracePoint.value.as< ArrayBF >();
		for( std::size_t offset = 0 ; offset < array.size() ; ++offset )
		{
			if( array[offset].is< TracePoint >() )
			{
				TracePoint & aTP = array[offset].to< TracePoint >();
				numerize(aTP);
			}
			else
			{
				if( ENV.eval(modelED, modelED.getSystemRID(), aTracePoint.value) )
				{
					aTracePoint.value = ENV.outVAL;
				}
				break;
			}
		}

	}
	else if( aTracePoint.value.is< BuiltinForm >() )
	{
		//!! NOTING
	}
	else if( ENV.eval(modelED, modelED.getSystemRID(), aTracePoint.value) )
	{
		aTracePoint.value = ENV.outVAL;
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , SOLVING , TRACE )
	AVM_OS_TRACE << "numeric(TracePoint):> " << std::endl;
	aTracePoint.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , SOLVING , TRACE )
}



} /* namespace sep */
