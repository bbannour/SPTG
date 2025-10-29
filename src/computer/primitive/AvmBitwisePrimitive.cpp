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

#include "AvmBitwisePrimitive.h"

#include <common/BF.h>

#include <computer/EvaluationEnvironment.h>

#include <fml/expression/AvmCode.h>

#include <fml/operator/Operator.h>
#include <fml/operator/OperatorManager.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE FORMAT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// INVARIANT:> only << second >>  could be << numeric<integer> >>

static void formtatBitwiseExpression(EvaluationEnvironment & ENV,
		const Operator * op, const BF & first, const BF & second)
{
	if( second.isInteger() && first.is< AvmCode >() &&
			first.to< AvmCode >().isOpCode(op) &&
			first.to< AvmCode >().second().isInteger() )
	{
		BF bresult;
		switch( op->getAvmOpCode() )
		{
			case AVM_OPCODE_BAND: // (x & m ) & n  ==  x & (m & n)
			{
				bresult = ExpressionConstructor::newInteger(second.isInteger() &
						first.to< AvmCode >().second().isInteger());
				break;
			}
			case AVM_OPCODE_BOR: // (x | m ) | n  ==  x | (m | n)
			{
				bresult = ExpressionConstructor::newInteger(second.isInteger() |
						first.to< AvmCode >().second().isInteger());
				break;
			}
			case AVM_OPCODE_BXOR: // (x ^ m ) ^ n  ==  x ^ (m ^ n)
			{
				bresult = ExpressionConstructor::newInteger(second.isInteger() ^
						first.to< AvmCode >().second().isInteger());

				break;
			}

			case AVM_OPCODE_LSHIFT: // (x << m ) << n  ==  x << (m + n)
			case AVM_OPCODE_RSHIFT: // (x >> m ) >> n  ==  x >> (m + n)
			{
				bresult = ExpressionConstructor::newInteger(second.isInteger() +
						first.to< AvmCode >().second().isInteger());

				break;
			}
			default :
			{
				AVM_OS_EXIT( FAILED )
						<< "Unexpected a bitwise operation << "
						<< first.str() << " " << op->getUnrestrictedName()
						<< " " << second.str() << " >>"
						<< SEND_EXIT;

				break;
			}
		}

		ENV.outVAL = ExpressionConstructor::newCode(op,
				first.to< AvmCode >().first(), bresult);
	}
	else
	{
		ENV.outVAL = ExpressionConstructor::newCode(op, first, second);
	}

//	ENV.outVAL = ENV.create(
//			ENV.outED.getRID(), op->getUnrestrictedName(), TypeManager::INTEGER, ENV.outVAL);
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE NOT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_BNOT::seval(EvaluationEnvironment & ENV)
{
	// AFA : si le parametre ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique BNOT#n a laquelle on associe
	// un AvmCode correspondant au BNOT de la valeur symbolique

	if( ENV.mARG->at(0).isInteger() )
	{
		// NOT OPERATION
		ENV.outVAL = ExpressionConstructor::newInteger(
				~ (ENV.mARG->at(0).toInteger()) );
	}
	else if( ENV.mARG->at(0).is< AvmCode >() &&
			ENV.mARG->at(0).to< AvmCode >().isOpCode( AVM_OPCODE_BNOT ) )
	{
		ENV.outVAL = ENV.mARG->at(0).to< AvmCode >().first();
	}
	else
	{
		ENV.outVAL = ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_BNOT, ENV.mARG->at(0));
//			ENV.outVAL = ENV.create(ENV.mARG->outED.getRID(), "BNOT",
//					TypeManager::INTEGER, ENV.mARG->at(0));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE AND
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_BAND::seval(EvaluationEnvironment & ENV)
{
	// AFA : si l'évaluation ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique BAND#n a laquelle
	// on associe un AvmCode correspondant au BAND des paramètres évaluées

	if ( ENV.mARG->at(0).isInteger() )
	{
		if ( ENV.mARG->at(1).isInteger() )
		{
			ENV.outVAL = ExpressionConstructor::newInteger(
					ENV.mARG->at(0).toInteger() & ENV.mARG->at(1).toInteger() );
		}
		else
		{
			formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BAND,
					ENV.mARG->at(1), ENV.mARG->at(0));
		}
	}
	else
	{
		formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BAND,
				ENV.mARG->at(0), ENV.mARG->at(1));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE OR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_BOR::seval(EvaluationEnvironment & ENV)
{
	// AFA : si l'évaluation ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique BOR#n a laquelle
	// on associe un AvmCode correspondant au BOR des paramètres évaluées

	if ( ENV.mARG->at(0).isInteger() )
	{
		if ( ENV.mARG->at(1).isInteger() )
		{
			ENV.outVAL = ExpressionConstructor::newInteger(
					ENV.mARG->at(0).toInteger() | ENV.mARG->at(1).toInteger() );
		}
		else
		{
			formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BOR,
					ENV.mARG->at(1), ENV.mARG->at(0));
		}
	}
	else
	{
		formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BOR,
				ENV.mARG->at(0), ENV.mARG->at(1));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE XOR
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_BXOR::seval(EvaluationEnvironment & ENV)
{
	// AFA : si l'évaluation ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique BXOR#n a laquelle
	// on associe un AvmCode correspondant au BXOR des paramètres évaluées

	if ( ENV.mARG->at(0).isInteger() )
	{
		if ( ENV.mARG->at(1).isInteger() )
		{
			ENV.outVAL = ExpressionConstructor::newInteger(
					ENV.mARG->at(0).toInteger() ^ ENV.mARG->at(1).toInteger() );
		}
		else
		{
			formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BXOR,
					ENV.mARG->at(1), ENV.mARG->at(0));
		}
	}
	else
	{
		formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_BXOR,
				ENV.mARG->at(0), ENV.mARG->at(1));
	}

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE LSHIFT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_LSHIFT::seval(EvaluationEnvironment & ENV)
{
	// AFA : si l'évaluation ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique LSHIFT#n a laquelle
	// on associe un AvmCode correspondant au LSHIFT des paramètres évaluées

	if ( ENV.mARG->at(0).isInteger() && ENV.mARG->at(1).isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newInteger(
				ENV.mARG->at(0).toInteger() << ENV.mARG->at(1).toInteger() );
	}
	else
	{
		formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_LSHIFT,
				ENV.mARG->at(0), ENV.mARG->at(1));
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///// BITWISE RSHIFT
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

bool AvmPrimitive_RSHIFT::seval(EvaluationEnvironment & ENV)
{
	// AFA : si l'évaluation ne se reduit pas a une valeur numerique
	// alors on cree une nouvelle valeur symbolique RSHIFT#n a laquelle
	// on associe un AvmCode correspondant au RSHIFT des paramètres évaluées

	if ( ENV.mARG->at(0).isInteger() && ENV.mARG->at(1).isInteger() )
	{
		ENV.outVAL = ExpressionConstructor::newInteger(
				ENV.mARG->at(0).toInteger() >> ENV.mARG->at(1).toInteger() );
	}
	else
	{
		formtatBitwiseExpression(ENV, OperatorManager::OPERATOR_RSHIFT,
				ENV.mARG->at(0), ENV.mARG->at(1));
	}

	return( true );
}



}
