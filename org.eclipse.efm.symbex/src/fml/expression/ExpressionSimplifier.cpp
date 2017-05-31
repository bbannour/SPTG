/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionSimplifier.h"

#include <fml/executable/BaseInstanceForm.h>

#include <fml/builtin/Boolean.h>
#include <fml/builtin/BuiltinForm.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// ARITHMETIC SIMPLIFIER
////////////////////////////////////////////////////////////////////////////////

BF ExpressionSimplifier::PLUS(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_PLUS, lhs, rhs) );
}

BF ExpressionSimplifier::PLUS(Vector< BF > & args)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_PLUS, args) );
}


BF ExpressionSimplifier::MINUS(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MINUS, lhs, rhs) );
}

BF ExpressionSimplifier::UMINUS(const BF & arg)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_UMINUS, arg) );
}


BF ExpressionSimplifier::MULT(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MULT, lhs, rhs) );
}

BF ExpressionSimplifier::MULT(Vector< BF > & args)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MULT, args) );
}


BF ExpressionSimplifier::POW(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_POW, lhs, rhs) );
}

BF ExpressionSimplifier::DIV(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_DIV, lhs, rhs) );
}




////////////////////////////////////////////////////////////////////////////////
// COMPARER SIMPLIFIER
////////////////////////////////////////////////////////////////////////////////

BF ExpressionSimplifier::EQ(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.isEQ( rhs ) )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
	}

	return( ExpressionConstructor::eqExpr(lhs, rhs) );
}

BF ExpressionSimplifier::NEQ(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.isEQ( rhs ) )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );
		}
	}

	return( ExpressionConstructor::neqExpr(lhs, rhs) );
}



BF ExpressionSimplifier::SEQ(const BF & lhs, const BF & rhs)
{
	return( ( lhs.isTEQ(rhs) || (lhs.str() == rhs.str()) )
			? ExpressionConstant::BOOLEAN_TRUE
			: ExpressionConstant::BOOLEAN_FALSE );
}

BF ExpressionSimplifier::NSEQ(const BF & lhs, const BF & rhs)
{
	return( ( lhs.isTEQ(rhs) || (lhs.str() == rhs.str()) )
			? ExpressionConstant::BOOLEAN_FALSE
			: ExpressionConstant::BOOLEAN_TRUE );
}



BF ExpressionSimplifier::LT(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.is< Number >() )
		{
			return( lhs.isEQ( rhs )
					? ExpressionConstant::BOOLEAN_TRUE
					: ExpressionConstant::BOOLEAN_FALSE );
		}
	}

	return( ExpressionConstructor::ltExpr(lhs, rhs) );
}

BF ExpressionSimplifier::LTE(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.is< BuiltinForm >() && rhs.is< BuiltinForm >() )
		{
			return( lhs.isEQ( rhs )
					? ExpressionConstant::BOOLEAN_TRUE
					: ExpressionConstant::BOOLEAN_FALSE );
		}
	}

	return( ExpressionConstructor::lteExpr(lhs, rhs) );
}

BF ExpressionSimplifier::GT(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.is< BuiltinForm >() && rhs.is< BuiltinForm >() )
		{
			return( lhs.isEQ( rhs )
					? ExpressionConstant::BOOLEAN_TRUE
					: ExpressionConstant::BOOLEAN_FALSE );
		}
	}

	return( ExpressionConstructor::gtExpr(lhs, rhs) );
}

BF ExpressionSimplifier::GTE(const BF & lhs, const BF & rhs)
{
	if( lhs.isTEQ(rhs) )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.classKind() == rhs.classKind() )
	{
		if( lhs.is< BuiltinForm >() && rhs.is< BuiltinForm >() )
		{
			return( lhs.isEQ( rhs )
					? ExpressionConstant::BOOLEAN_TRUE
					: ExpressionConstant::BOOLEAN_FALSE );
		}
	}

	return( ExpressionConstructor::gteExpr(lhs, rhs) );
}



////////////////////////////////////////////////////////////////////////////////
// LOGIC SIMPLIFIER
////////////////////////////////////////////////////////////////////////////////

BF ExpressionSimplifier::NOT(const BF & arg)
{
	if( arg.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( arg.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_NOT, arg) );
	}
}

BF ExpressionSimplifier::AND(const BF & lhs, const BF & rhs)
{
	if( lhs.isEqualFalse() || rhs.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( lhs.isEqualTrue() )
	{
		return( rhs );
	}
	else if( rhs.isEqualTrue() || (lhs == rhs) )
	{
		return( lhs );
	}
	else
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_AND, lhs, rhs) );
	}
}

BF ExpressionSimplifier::AND(Vector< BF > & args)
{
	BFCode resEXPR( OperatorManager::OPERATOR_AND );

	AvmCode::const_iterator itRes;
	AvmCode::const_iterator endRes;

	AvmCode::const_iterator itArg = args.begin();
	AvmCode::const_iterator endArg = args.end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( (*itArg).isEqualFalse() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );
		}
		else if( (*itArg).isNotEqualTrue() )
		{
			endRes = resEXPR->end();
			for( itRes = resEXPR->begin() ; itRes != endRes ; ++itRes )
			{
				if( (*itArg).isEQ( *itRes )  )
				{
					break;
				}
			}

			if( itRes == endRes )
			{
				resEXPR->append( (*itArg) );
			}
		}
	}

	if( resEXPR->populated() )
	{
		return( resEXPR );
	}
	else if( resEXPR->nonempty() )
	{
		return( resEXPR->first() );
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


BF ExpressionSimplifier::NAND(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_AND, lhs, rhs) );
}

BF ExpressionSimplifier::NAND(Vector< BF > & args)
{
	BFCode resEXPR( OperatorManager::OPERATOR_NAND );

	AvmCode::const_iterator itRes;
	AvmCode::const_iterator endRes;

	AvmCode::const_iterator itArg = args.begin();
	AvmCode::const_iterator endArg = args.end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( (*itArg).isEqualFalse() )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
		else if( (*itArg).isNotEqualTrue() )
		{
			endRes = resEXPR->end();
			for( itRes = resEXPR->begin() ; itRes != endRes ; ++itRes )
			{
				if( (*itArg).isEQ( *itRes )  )
				{
					break;
				}
			}

			if( itRes == endRes )
			{
				resEXPR->append( (*itArg) );
			}
		}
	}

	if( resEXPR->populated() )
	{
		return( resEXPR );
	}
	else if( resEXPR->nonempty() )
	{
		return( resEXPR->first() );
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}


BF ExpressionSimplifier::XAND(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XAND, lhs, rhs) );
}

BF ExpressionSimplifier::XAND(Vector< BF > & args)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XAND, args) );
}




BF ExpressionSimplifier::OR(const BF & lhs, const BF & rhs)
{
	if( lhs.isEqualTrue() || rhs.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( lhs.isEqualFalse() )
	{
		return( rhs );
	}
	else if( rhs.isEqualFalse() || (lhs == rhs) )
	{
		return( lhs );
	}
	else
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_OR, lhs, rhs) );
	}
}

BF ExpressionSimplifier::OR(Vector< BF > & args)
{
	BFCode resEXPR( OperatorManager::OPERATOR_OR );

	AvmCode::const_iterator itRes;
	AvmCode::const_iterator endRes;

	AvmCode::const_iterator itArg = args.begin();
	AvmCode::const_iterator endArg = args.end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( (*itArg).isEqualTrue() )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
		else if( (*itArg).isNotEqualFalse() )
		{
			endRes = resEXPR->end();
			for( itRes = resEXPR->begin() ; itRes != endRes ; ++itRes )
			{
				if( (*itArg).isEQ( *itRes )  )
				{
					break;
				}
			}

			if( itRes == endRes )
			{
				resEXPR->append( (*itArg) );
			}
		}
	}

	if( resEXPR->populated() )
	{
		return( resEXPR );
	}
	else if( resEXPR->nonempty() )
	{
		return( resEXPR->first() );
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


BF ExpressionSimplifier::NOR(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_NOR, lhs, rhs) );
}

BF ExpressionSimplifier::NOR(Vector< BF > & args)
{
	BFCode resEXPR( OperatorManager::OPERATOR_NOR );

	AvmCode::const_iterator itRes;
	AvmCode::const_iterator endRes;

	AvmCode::const_iterator itArg = args.begin();
	AvmCode::const_iterator endArg = args.end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( (*itArg).isEqualTrue() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE );
		}
		else if( (*itArg).isNotEqualFalse() )
		{
			endRes = resEXPR->end();
			for( itRes = resEXPR->begin() ; itRes != endRes ; ++itRes )
			{
				if( (*itArg).isEQ( *itRes )  )
				{
					break;
				}
			}

			if( itRes == endRes )
			{
				resEXPR->append( (*itArg) );
			}
		}
	}

	if( resEXPR->populated() )
	{
		return( resEXPR );
	}
	else if( resEXPR->nonempty() )
	{
		return( resEXPR->first() );
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}



BF ExpressionSimplifier::XOR(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XOR, lhs, rhs) );
}

BF ExpressionSimplifier::XOR(Vector< BF > & args)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XOR, args) );
}


BF ExpressionSimplifier::XNOR(const BF & lhs, const BF & rhs)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XNOR, lhs, rhs) );
}

BF ExpressionSimplifier::XNOR(Vector< BF > & args)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_XNOR, args) );
}




////////////////////////////////////////////////////////////////////////////////
// PREDICATE SIMPLIFIER
////////////////////////////////////////////////////////////////////////////////

BF ExpressionSimplifier::simplif(const BF & expr)
{
	if ( expr.valid() )
	{
		return( expr );

		AVM_OS_WARNING_ALERT
				<< "Todo: simplif the Expression\n"
				<< expr.toString( AVM_TAB1_INDENT )
				<< SEND_ALERT;
	}

	return( expr );
}



BF ExpressionSimplifier::simplif_and(const BF & arg0, const BF & arg1)
{
	if( arg0.isEqualFalse() || arg1.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( arg1.isEqualTrue() )
	{
		return( arg0 );
	}
	else if( arg0.isEqualTrue() || (arg0 == arg1) )
	{
		return( arg1 );
	}

	else
	{
		return( ExpressionSimplifier::simplif(
				ExpressionConstructor::andExpr(arg0, arg1)) );
	}
}


BF ExpressionSimplifier::simplif_or(const BF & arg0, const BF & arg1)
{
	if( arg0.isEqualTrue() || arg1.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( arg1.isEqualFalse() )
	{
		return( arg0 );
	}
	else if( arg0.isEqualFalse() || (arg0 == arg1) )
	{
		return( arg1 );
	}

	else
	{
		return( ExpressionSimplifier::simplif(
				ExpressionConstructor::orExpr(arg0, arg1)) );
	}
}


BF ExpressionSimplifier::simplif_not(const BF & arg0)
{
	if( arg0.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( arg0.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}

	else
	{
		return( ExpressionSimplifier::simplif(
				ExpressionConstructor::notExpr(arg0))  );
	}
}



} /* namespace sep */
