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

#include "BaseAvmPrimitive.h"


#include <computer/primitive/AvmPrimitiveProcessor.h>

#include <computer/EvaluationEnvironment.h>
#include <computer/ExecutionEnvironment.h>

#include <fml/expression/ExpressionConstructor.h>



namespace sep
{

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// RESUME
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool BaseAvmPrimitive::resume(ExecutionEnvironment & ENV)
{
	AVM_OS_FATAL_ERROR_EXIT
			<< "Unimplemented resume instruction for :>\n"
			<< ENV.inFORM.toString( AVM_TAB1_INDENT )
			<< SEND_EXIT;

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool BaseAvmPrimitive::seval(EvaluationEnvironment & ENV)
{
	BFCode regEXPR( ENV.inCODE->getOperator() );

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.seval( itOperand );

		regEXPR->append( ENV.outVAL );
	}

	ENV.outVAL = regEXPR;

	return( true );
}

/*
bool BaseAvmPrimitive::meval(EvaluationEnvironment & ENV)
{
	long idx = 0;
	long endIdx = ENV.outEDS.size();
	BFCodeVector regEXPR( endIdx );
	for( idx = 0 ; idx < endIdx ; ++idx )
	{
		regEXPR[ idx ] = ExpressionConstructor::newCode(
				ENV.inCODE->getOperator() );
	}

	for( const auto & itOperand : ENV.inCODE.getOperands() )
	{
		ENV.meval( itOperand );

		if( (long)(ENV.outEDS.size()) > endIdx )
		{
			regEXPR.resize( ENV.outEDS.size() );
			for( idx = ENV.outEDS.size() - 1 ; idx >= endIdx ; --idx )
			{
				regEXPR[ idx ] = regEXPR[ ENV.mOffsets[ idx ] ]->clone();

				regEXPR[ idx ]->append( ENV.outCODES[ idx ] );
			}

			endIdx = ENV.outEDS.size();
		}
		else
		{
			idx = endIdx - 1;
		}

		for( ; idx >= 0 ; --idx )
		{
			regEXPR[ idx ]->append( ENV.outCODES[ idx ] );
		}
	}

	for( idx = 0 ; idx < endIdx ; ++idx )
	{
		ENV.outCODES[ idx ] = regEXPR[ idx ];
	}

	return( true );
}
*/

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// EVAL x 2
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool BaseAvmPrimitive::sevalx2(EvaluationEnvironment & ENV)
{
	if( BaseAvmPrimitive::seval(ENV) )
	{
		return( ENV.seval(ENV.outVAL) );
	}

	return( false );
}


}
