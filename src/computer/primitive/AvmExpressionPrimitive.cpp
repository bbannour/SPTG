/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 sept. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmExpressionPrimitive.h"

#include <common/BF.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/expression/ExpressionConstructorImpl.h>

namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// COMPARISON PLUS
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_EvalExpressionALU::seval(EvaluationEnvironment & ENV)
{
	AvmCode * inCODE = ENV.inCODE;

	const Operator * inOperator = inCODE->getOperator();

	switch( inCODE->size() )
	{
		case 0:
		{
			ENV.outVAL = ENV.inFORM;

			return( true );
		}

		case 1:
		{
			if( ENV.seval( inCODE->first() ) )
			{
				ENV.outVAL = ExpressionConstructor::
						newExpr(inOperator, ENV.outVAL);

				return( true );
			}

			return( false );
		}

		case 2:
		{
			BF leftVAL;

			if( ENV.seval( inCODE->first() ) )
			{
				leftVAL = ENV.outVAL;

				if( ENV.sevalChained( inCODE->second() ) )
				{
					ENV.outVAL = ExpressionConstructor::
							newExpr(inOperator, leftVAL, ENV.outVAL);

					return( true );
				}
			}

			return( false );
		}

		default:
		{
			BFVector outVALs;

			AvmCode::const_iterator itOperand  = inCODE->begin();
			AvmCode::const_iterator endOperand = inCODE->end();

			if( ENV.seval( *itOperand ) )
			{
				outVALs.append( ENV.outVAL );
			}
			else
			{
				return( false );
			}
			for( ++itOperand ; itOperand != endOperand ; ++itOperand )
			{
				if( ENV.sevalChained( *itOperand ) )
				{
					outVALs.append( ENV.outVAL );
				}
				else
				{
					return( false );
				}
			}

			ENV.outVAL = ExpressionConstructor::newExpr(inOperator, outVALs);

			return( true );
		}
	}

	return( true );
}


} /* namespace sep */
