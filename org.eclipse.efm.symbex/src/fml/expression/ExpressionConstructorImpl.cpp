/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juin 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionConstructorImpl.h"

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/numeric/Numeric.h>


namespace sep
{

/**
 * SPECIFIC AVMCODE EXPRESSION
 */
static bool appendLogicTerm(const BF & term,
		AvmCode::this_container_type & resArgs)
{
	if( resArgs.empty() )
	{
		resArgs.append( term );
	}
	else
	{
		AvmCode * aCode;

		int cmpResult;

		bool coef1;
		BF expr1;

		bool coef2 = true;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			aCode = term.to_ptr< AvmCode >();

			if( aCode->isOpCode(AVM_OPCODE_NOT) )
			{
				coef2 = false;
				expr2 = aCode->first();
			}
		}

		AvmCode::iterator itArg = resArgs.begin();
		AvmCode::iterator endArg = resArgs.end();
		for( ; itArg != endArg ; ++itArg )
		{
			//case A * (<sign> B) + C + ...  with  (<sign> B)
			coef1 = true;
			expr1 = (*itArg);
			if( (*itArg).is< AvmCode >() )
			{
				aCode = (*itArg).to_ptr< AvmCode >();

				if( aCode->isOpCode(AVM_OPCODE_NOT) )
				{
					coef1 = false;
					expr1 = aCode->first();
				}
			}

			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				return( coef1 == coef2 );
			}
			else if( cmpResult > 0 )
			{
				resArgs.insert(itArg, term);

				return( true );
			}
		}

		resArgs.append( term );
	}

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// AND EXPRESSION
////////////////////////////////////////////////////////////////////////////////

inline static bool andFlatExpr(const BF & term,
		AvmCode::this_container_type & resArgs)
{
	if( term.is< AvmCode >() )
	{
		AvmCode * argCode = term.to_ptr< AvmCode >();

		if( term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_AND) )
		{
			AvmCode::const_iterator itArg = argCode->begin();
			AvmCode::const_iterator endArg = argCode->end();
			for( ; itArg != endArg ; ++itArg )
			{
				if( (*itArg).isEqualTrue() )
				{
					//continue;
				}
				else if( (*itArg).isEqualFalse() )
				{
					return( false );
				}
				else if( not appendLogicTerm(*itArg, resArgs) )
				{
					return( false );
				}
			}

			return( true );
		}
		else
		{
			return( appendLogicTerm(term, resArgs) );
		}
	}
	else
	{
		return( appendLogicTerm(term, resArgs) );
	}
}


BF ExpressionConstructorNative::andExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.isEqualFalse() || arg1.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( arg0.isEqualTrue() )
	{
		return( arg1 );
	}
	else if( arg1.isEqualTrue() )
	{
		return( arg0 );
	}

	else
	{
		BFCode resCode( OperatorManager::OPERATOR_AND );

		if( andFlatExpr(arg0, resCode->getArgs()) )
		{
			if( andFlatExpr(arg1, resCode->getArgs()) )
			{
				if( resCode->empty() )
				{
					return( ExpressionConstant::BOOLEAN_TRUE );
				}
				else
				{
					return( resCode->singleton() ? resCode->first() : resCode );
				}
			}
		}

		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}


BF ExpressionConstructorNative::andExpr(
		const AvmCode::this_container_type & listOfArg)
{
	if( listOfArg.nonempty() )
	{
		BFCode resCode( OperatorManager::OPERATOR_AND );

		AvmCode::const_iterator itArg = listOfArg.begin();
		AvmCode::const_iterator endArg = listOfArg.end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).isEqualTrue() )
			{
				//continue;
			}
			else if( (*itArg).isEqualFalse() )
			{
				return( ExpressionConstant::BOOLEAN_FALSE );
			}
			else if( not andFlatExpr(*itArg, resCode->getArgs()) )
			{
				return( ExpressionConstant::BOOLEAN_FALSE );
			}
		}

		if( resCode->empty() )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
		else
		{
			return( resCode->singleton() ? resCode->first() : resCode );
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ExpressionConstructorNative::andExpr(...) "
					"with an empty argument list"
				<< SEND_EXIT;

		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}


////////////////////////////////////////////////////////////////////////////////
// OR EXPRESSION
////////////////////////////////////////////////////////////////////////////////

inline static bool orFlatExpr(const BF & term,
		AvmCode::this_container_type & resArgs)
{
	if( term.is< AvmCode >() )
	{
		AvmCode * argCode = term.to_ptr< AvmCode >();

		if( term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_OR) )
		{
			AvmCode::const_iterator itArg = argCode->begin();
			AvmCode::const_iterator endArg = argCode->end();
			for( ; itArg != endArg ; ++itArg )
			{
				if( (*itArg).isEqualTrue() )
				{
					return( false );
				}
				else if( (*itArg).isEqualFalse() )
				{
					//continue;
				}
				else if( not appendLogicTerm(*itArg, resArgs) )
				{
					return( false );
				}
			}

			return( true );
		}
		else
		{
			return( appendLogicTerm(term, resArgs) );
		}
	}
	else
	{
		return( appendLogicTerm(term, resArgs) );
	}
}


BF ExpressionConstructorNative::orExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.isEqualTrue() || arg1.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( arg0.isEqualFalse() )
	{
		return( arg1 );
	}
	else if( arg1.isEqualFalse() )
	{
		return( arg0 );
	}

	else
	{
		BFCode resCode( OperatorManager::OPERATOR_OR );

		if( orFlatExpr(arg0, resCode->getArgs()) )
		{
			if( orFlatExpr(arg1, resCode->getArgs()) )
			{
				if( resCode->empty() )
				{
					return( ExpressionConstant::BOOLEAN_TRUE );
				}
				else
				{
					return( resCode->singleton() ? resCode->first() : resCode );
				}
			}
		}

		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


BF ExpressionConstructorNative::orExpr(
		const AvmCode::this_container_type & listOfArg)
{
	if( listOfArg.nonempty() )
	{
		BFCode resCode( OperatorManager::OPERATOR_OR );

		AvmCode::const_iterator itArg = listOfArg.begin();
		AvmCode::const_iterator endArg = listOfArg.end();
		for( ; itArg != endArg ; ++itArg )
		{
			if( (*itArg).isEqualTrue() )
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
			else if( (*itArg).isEqualFalse() )
			{
				//continue;
			}
			else if( not orFlatExpr(*itArg, resCode->getArgs()) )
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
		}

		if( resCode->empty() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE);
		}
		else
		{
			return( resCode->singleton() ? resCode->first() : resCode );
		}
	}
	else
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "Unexpected ExpressionConstructorNative::orExpr(...) "
					"with an empty argument list"
				<< SEND_EXIT;

		return( ExpressionConstant::BOOLEAN_FALSE);
	}
}


////////////////////////////////////////////////////////////////////////////////////
// QUANTIFIER EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::existExpr(
		const BF & boundVar, const BF & formula)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_EXIST, boundVar, formula) );
}

BF ExpressionConstructorNative::existExpr(
		const AvmCode::this_container_type & listOfArg)
{
	return( ExpressionConstructor::newCode(
		OperatorManager::OPERATOR_EXIST, listOfArg) );
}


BF ExpressionConstructorNative::forallExpr(
		const BF & boundVar, const BF & formula)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_FORALL, boundVar, formula) );
}

BF ExpressionConstructorNative::forallExpr(
		const AvmCode::this_container_type & listOfArg)
{
	return( ExpressionConstructor::newCode(
		OperatorManager::OPERATOR_FORALL, listOfArg) );
}


////////////////////////////////////////////////////////////////////////////////////
// NOT EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::notExpr(const BF & arg)
{
	if( arg.isEqualTrue() )
	{
		return( ExpressionConstant::BOOLEAN_FALSE );
	}
	else if( arg.isEqualFalse() )
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
	else if( arg.is< AvmCode >() )
	{
		AvmCode * aCode = arg.to_ptr< AvmCode >();

		switch( aCode->getAvmOpCode() )
		{
			case AVM_OPCODE_EQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_NEQ, aCode->getArgs()) );
			}
			case AVM_OPCODE_NEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_EQ, aCode->getArgs()) );
			}

			case AVM_OPCODE_SEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_NSEQ, aCode->getArgs()) );
			}
			case AVM_OPCODE_NSEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_SEQ, aCode->getArgs()) );
			}

			case AVM_OPCODE_LT:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_GTE, aCode->getArgs()) );
			}
			case AVM_OPCODE_LTE:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_GT, aCode->getArgs()) );
			}
			case AVM_OPCODE_GT:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_LTE, aCode->getArgs()) );
			}
			case AVM_OPCODE_GTE:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_LT, aCode->getArgs()) );
			}

			case AVM_OPCODE_NOT:
			{
				return( aCode->first() );
			}

			case AVM_OPCODE_AND:
			{
				BFCode resCode( OperatorManager::OPERATOR_OR );

				AvmCode::const_iterator itArg = aCode->begin();
				AvmCode::const_iterator endArg = aCode->end();
				for( ; itArg != endArg ; ++itArg )
				{
					resCode->append( notExpr( *itArg ) );
				}

				return( resCode );
			}
			case AVM_OPCODE_NAND:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_AND, aCode->getArgs()) );
			}

//			case AVM_OPCODE_XAND:
//			{
//				return( ExpressionConstructor::newCode(
//						OperatorManager::OPERATOR_OR, aCode->getArgs()) );
//			}

			case AVM_OPCODE_OR:
			{
				BFCode resCode( OperatorManager::OPERATOR_AND );

				AvmCode::const_iterator itArg = aCode->begin();
				AvmCode::const_iterator endArg = aCode->end();
				for( ; itArg != endArg ; ++itArg )
				{
					resCode->append( notExpr( *itArg ) );
				}

				return( resCode );
			}
			case AVM_OPCODE_NOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_OR, aCode->getArgs()) );
			}

			case AVM_OPCODE_XOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_XNOR, aCode->getArgs()) );
			}
			case AVM_OPCODE_XNOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_XOR, aCode->getArgs()) );
			}

			default:
			{
				break;
			}
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_NOT, arg) );
}


////////////////////////////////////////////////////////////////////////////////////
// COMPARE EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

template< typename OP_T > BF compare(
		const BF & lhArg, const BF & rhArg, Operator * cmpOp, OP_T cmp)
{
	//case X rel_op Y  ==> diff := X - Y
	BF diff = ExpressionConstructorNative::minusExpr(lhArg, rhArg);

	//case diff = <num>
	if( diff.is< Number >() )
	{
		return( ExpressionConstructorNative::newBoolean(
				cmp(diff.to_ptr< Number >()->sign(), 0) ) );
	}

	//case diff = <term>
	else if( diff.is< AvmCode >() )
	{
		AvmCode * diffCode = diff.to_ptr< AvmCode >();

		//case diff = A + B + ...
		if( diffCode->isOpCode(AVM_OPCODE_PLUS) )
		{
			BFCode lhCode( OperatorManager::OPERATOR_PLUS );
			BFCode rhCode( OperatorManager::OPERATOR_PLUS );

			AvmCode::const_iterator itArg = diffCode->begin();
			AvmCode::const_iterator endArg = diffCode->end();
			for( ; itArg != endArg ; ++itArg )
			{
				//case diff = A + B + ... + <num>
				if( (*itArg).is< Number >() )
				{
					rhCode->append( ExpressionConstructorNative::
							uminusExpr( *itArg ) );
				}

				else if( (*itArg).is< AvmCode >() )
				{
					AvmCode * argCode = (*itArg).to_ptr< AvmCode >();

					//case diff = (- A) + B + C +...
					if( argCode->isOpCode(AVM_OPCODE_UMINUS) )
					{
						rhCode->append( argCode->first() );
					}
					//case diff = (- <num> * X * Y * ...) + A + B + ...
					else if( argCode->isOpCode(AVM_OPCODE_MULT)
							&& argCode->first().is< Number >()
							&& argCode->first().to_ptr<
									Number >()->strictlyNegative() )
					{
						rhCode->append( ExpressionConstructorNative::
								uminusExpr( *itArg ) );
					}
					else
					{
						lhCode->append( *itArg );
					}
				}
				else
				{
					lhCode->append( *itArg );
				}
			}

			BFCode cmpCode( cmpOp );

			if( lhCode->singleton() )
			{
				cmpCode->append( lhCode->first() );
			}
			else if( lhCode->populated() )
			{
				cmpCode->append( lhCode );
			}
			else
			{
				cmpCode->append( ExpressionConstant::INTEGER_ZERO );
			}

			if( rhCode->singleton() )
			{
				cmpCode->append( rhCode->first() );
			}
			else if( rhCode->populated() )
			{
				cmpCode->append( rhCode );
			}
			else
			{
				cmpCode->append( ExpressionConstant::INTEGER_ZERO );
			}

			return( cmpCode );
		}
	}

	return( ExpressionConstructor::newCode(cmpOp, diff,
			ExpressionConstant::INTEGER_ZERO) );
}


BF ExpressionConstructorNative::eqExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_EQ, std::equal_to<int>()) );
}

BF ExpressionConstructorNative::neqExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_NEQ, std::not_equal_to<int>()) );
}


BF ExpressionConstructorNative::gtExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_GT, std::greater<int>()) );
}


BF ExpressionConstructorNative::gteExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_GTE, std::greater_equal<int>()) );
}

BF ExpressionConstructorNative::ltExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_LT, std::less<int>()) );
}

BF ExpressionConstructorNative::lteExpr(const BF & arg0, const BF & arg1)
{
	return( compare(arg0, arg1,
			OperatorManager::OPERATOR_LTE, std::less_equal<int>()) );
}


////////////////////////////////////////////////////////////////////////////////
// ADD EXPRESSION
// Normalization : <term> + <term> + ... + <num>
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::addNumber(const BF & num0, const BF & num1)
{
	if( num0.is< Number >() )
	{
		if( num0.to_ptr< Number >()->isZero() )
		{
			return( num1 );
		}
		else if( num1.is< Number >() )
		{
			if( num1.to_ptr< Number >()->isZero() )
			{
				return( num0 );
			}

			return( ExpressionConstructor::newNumeric(
					Numeric::acquire( num0.to_ptr< Number >() ).add(
					Numeric::acquire( num1.to_ptr< Number >() ) ) ) );
		}

		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_PLUS, num1, num0) );
	}
	else if( num1.is< Number >() )
	{
		if( num1.to_ptr< Number >()->isZero() )
		{
			return( num0 );
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_PLUS, num0, num1) );
}


static void addExpr(const BF & term,
		AvmCode::this_container_type & resArgs, Numeric & resNumberArg)
{
	if( term.is< Number >() )
	{
		resNumberArg += term;
	}
	else if( resArgs.empty() )
	{
		resArgs.append( term );
	}
	else
	{
		AvmCode * aCode;

		Numeric coef_sum;

		int cmpResult;

		Numeric coef1;
		BF expr1;

		Numeric coef2 = ExpressionConstant::INTEGER_ONE;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			aCode = term.to_ptr< AvmCode >();

			if( aCode->isOpCode(AVM_OPCODE_MULT)
				&& aCode->first().is< Number >() )
			{
				coef2 = aCode->first();
				if( aCode->size() == 2 )
				{
					expr2 = aCode->second();
				}
				else
				{
					expr2 = ExpressionConstructor::newCodeTail(
							OperatorManager::OPERATOR_MULT, aCode->getArgs());
				}
			}
			else if( aCode->isOpCode(AVM_OPCODE_UMINUS) )
			{
				coef2 = ExpressionConstant::INTEGER_MINUS_ONE;
				expr2 = aCode->first();
			}
		}

		AvmCode::iterator itArg = resArgs.begin();
		AvmCode::iterator endArg = resArgs.end();
		for( ; itArg != endArg ; ++itArg )
		{
			//case A + (<num>*B) + C + ... with  <num> * B
			coef1 = ExpressionConstant::INTEGER_ONE;
			expr1 = (*itArg);
			if( (*itArg).is< AvmCode >() )
			{
				aCode = (*itArg).to_ptr< AvmCode >();

				if( aCode->isOpCode(AVM_OPCODE_MULT)
					&& aCode->first().is< Number >() )
				{
					coef1 = aCode->first();
					if( aCode->size() == 2 )
					{
						expr1 = aCode->second();
					}
					else
					{
						expr1 = ExpressionConstructor::newCodeTail(
								OperatorManager::OPERATOR_MULT, aCode->getArgs());
					}
				}
				else if( aCode->isOpCode(AVM_OPCODE_UMINUS) )
				{
					coef1 = ExpressionConstant::INTEGER_MINUS_ONE;
					expr1 = aCode->first();
				}
			}

			//==> A + (<num> + <num>)*B + C + ...
			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				coef_sum = ExpressionConstructorNative::addNumber(coef1, coef2);
				if( coef_sum.isZero() )
				{
					itArg = resArgs.erase( itArg );
				}
				else
				{
					(*itArg) = ExpressionConstructorNative::multExpr(
							coef_sum, expr1);
				}

				return;
			}
			else if( cmpResult > 0 )
			{
				resArgs.insert(itArg, term);

				return;
			}
		}

		resArgs.append( term );
	}
}


inline static void addFlatExpr(const BF & term,
		AvmCode::this_container_type & resArgs, Numeric & resNumberArg)
{
	if( term.is< AvmCode >() )
	{
		AvmCode * argCode = term.to_ptr< AvmCode >();

		if(term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_PLUS) )
		{
			AvmCode::const_iterator itArg = argCode->begin();
			AvmCode::const_iterator endArg = argCode->end();
			for( ; itArg != endArg ; ++itArg )
			{
				addExpr(*itArg, resArgs, resNumberArg);
			}
		}
		else
		{
			addExpr(term, resArgs, resNumberArg);
		}
	}
	else
	{
		addExpr(term, resArgs, resNumberArg);
	}
}


BF ExpressionConstructorNative::addExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.isEqualZero() )
	{
		return( arg1 );
	}
	else if( arg1.isEqualZero() )
	{
		return( arg0 );
	}
	else if( arg0.is< Number >() && arg1.is< Number >() )
	{
		return( addNumber(arg0, arg1) );
	}
	else
	{
		BFCode resCode( OperatorManager::OPERATOR_PLUS );

		Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

		addFlatExpr(arg0, resCode->getArgs(), numTerm);

		addFlatExpr(arg1, resCode->getArgs(), numTerm);

		if( resCode->empty() )
		{
			return( numTerm );
		}
		else if( not numTerm.isZero() )
		{
			resCode->append( numTerm );
		}

		return( resCode->singleton() ? resCode->first() : resCode );
	}
}


BF ExpressionConstructorNative::addExpr(
		const AvmCode::this_container_type & listOfArg)
{
	BFCode resCode( OperatorManager::OPERATOR_PLUS );

	Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

	AvmCode::const_iterator itArg = listOfArg.begin();
	AvmCode::const_iterator endArg = listOfArg.end();
	for( ; itArg != endArg ; ++itArg )
	{
		addFlatExpr(*itArg, resCode->getArgs(), numTerm);
	}

	if( resCode->empty() )
	{
		return( numTerm );
	}
	else if( not numTerm.isZero() )
	{
		resCode->append( numTerm );
	}

	return( resCode->singleton() ? resCode->first() : resCode );
}



////////////////////////////////////////////////////////////////////////////////
// MINUS EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::minusExpr(const BF & arg0, const BF & arg1)
{
	return( addExpr(arg0, uminusExpr(arg1)) );
}


////////////////////////////////////////////////////////////////////////////////
// UMINUS EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::uminusExpr(const BF & arg)
{
//	switch( arg.classKind() )
//	{
//		//case - <integer>
//		case FORM_BUILTIN_INTEGER_KIND:
//		{
//			BF res = arg;
//			res.makeWritable();
//			res.to_ptr< Integer >()->uminus();
//
//			return( res );
//		}
//
//		//case - <rational>
//		case FORM_BUILTIN_RATIONAL_KIND:
//		{
//			BF res = arg;
//			res.makeWritable();
//			res.to_ptr< Rational >()->uminus();
//
//			return( res );
//		}
//
//		//case - <float>
//		case FORM_BUILTIN_FLOAT_KIND:
//		{
//			BF res = arg;
//			res.makeWritable();
//			res.to_ptr< Float >()->uminus();
//
//			return( res );
//		}
//
//		default:
//		{
//			break;
//		}
//	}


	if( arg.is< Number >() )
	{
		return( ExpressionConstructor::newNumeric(
				Numeric::acquire( arg.to_ptr< Number >() ).uminus() ) );
	}

	//case - <term>
	else if( arg.is< AvmCode >() )
	{
		AvmCode * aCode = arg.to_ptr< AvmCode >();

		switch( aCode->getAvmOpCode() )
		{
			//case - (A + B + ...)
			case AVM_OPCODE_PLUS:
			{
				BFCode resCode( OperatorManager::OPERATOR_PLUS );

				AvmCode::const_iterator itArg = aCode->begin();
				AvmCode::const_iterator endArg = aCode->end();
				for( ; itArg != endArg ; ++itArg )
				{
					resCode->append( uminusExpr( *itArg ) );
				}

				return( resCode );
			}

			//case - (A - B - ...)
			case AVM_OPCODE_MINUS:
			{
				AvmCode::const_iterator itArg = aCode->begin();

				BFCode resCode( OperatorManager::OPERATOR_PLUS,
						uminusExpr( *itArg ) );

				AvmCode::const_iterator endArg = aCode->end();
				for( ++itArg ; itArg != endArg ; ++itArg )
				{
					resCode->append( *itArg );
				}

				return( resCode );
			}

			//case - (- <term>)
			case AVM_OPCODE_UMINUS:
			{
				return( aCode->first() );
			}

			//case - (A * B * ...)
			case AVM_OPCODE_MULT:
			{
				//case +- (<num> * A * B * ...)
				if( aCode->first().is< Number >() )
				{
					AvmCode::const_iterator itArg = aCode->begin();

					BFCode resCode( OperatorManager::OPERATOR_MULT );

					if( not (*itArg).to_ptr< Number >()->isNegativeOne() )
					{
						resCode->append( uminusExpr( *itArg ) );
					}

					AvmCode::const_iterator endArg = aCode->end();
					for( ++itArg ; itArg != endArg ; ++itArg )
					{
						resCode->append( *itArg );
					}

					//==> (- <num>) * A * B * ...
					return( resCode );
				}

				//==> (- 1) * A * B * ...
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_MULT ,
						ExpressionConstant::INTEGER_MINUS_ONE,
						aCode->getArgs()) );
			}

			//case - (A / B )
			case AVM_OPCODE_DIV:
			{
				//==> ((- 1) * A) / B
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_DIV ,
						uminusExpr( aCode->first() ), aCode->second()) );
			}

			default:
			{
				break;
			}
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_UMINUS, arg) );
}



////////////////////////////////////////////////////////////////////////////////
// MULT EXPRESSION
// Normalization : <num> * <term> * <term> * ...
////////////////////////////////////////////////////////////////////////////////

static bool multExpr(const BF & term,
		AvmCode::this_container_type & resMultArgs,
		Numeric & resNumberCoef, bool & expandAddExpr)
{
	if( resNumberCoef.isZero() )
	{
		return( false );
	}
	else if( term.is< Number >() )
	{
		if( term.to_ptr< Number >()->isZero() )
		{
			resNumberCoef = ExpressionConstant::INTEGER_ZERO;

			return( false );
		}
		else
		{
			resNumberCoef *= term;
		}
	}
	else if( resMultArgs.empty() )
	{
		if( term.is< AvmCode >() &&
			term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_PLUS) )
		{
			resMultArgs.append( term.to_ptr< AvmCode >()->getArgs() );

			expandAddExpr = true;
		}
		else
		{
			resMultArgs.append( term );
		}
	}
	else if( expandAddExpr )
	{
		AvmCode::this_container_type resAddArgs( resMultArgs );
		resMultArgs.clear();

		Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

		AvmCode::const_iterator itArg = resAddArgs.begin();
		AvmCode::const_iterator endArg = resAddArgs.end();
		for( ; itArg != endArg ; ++itArg )
		{
			addFlatExpr(ExpressionConstructorNative::multExpr(term, *itArg),
					resMultArgs, numTerm);
		}

		if( not numTerm.isZero() )
		{
			if( resMultArgs.empty() )
			{
				resMultArgs.append( numTerm );
			}
		}
	}
	else if( term.is< AvmCode >() &&
			term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_PLUS) )
	{
		BF multArg = resMultArgs.singleton() ? resMultArgs.first() :
				ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_MULT, resMultArgs);

		resMultArgs.clear();
		Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

		AvmCode * aCode = term.to_ptr< AvmCode >();
		AvmCode::const_iterator itArg = aCode->begin();
		AvmCode::const_iterator endArg = aCode->end();
		for( ; itArg != endArg ; ++itArg )
		{
			addFlatExpr(ExpressionConstructorNative::multExpr(multArg, *itArg),
					resMultArgs, numTerm);
		}

		if( not numTerm.isZero() )
		{
			if( resMultArgs.empty() )
			{
				resMultArgs.append( numTerm );
			}
		}

		expandAddExpr = true;
	}

	else
	{
		AvmCode * aCode;

		Numeric coef_sum;

		int cmpResult;

		Numeric exponent1;
		BF expr1;

		Numeric exponent2 = ExpressionConstant::INTEGER_ONE;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			aCode = term.to_ptr< AvmCode >();

			if( aCode->isOpCode(AVM_OPCODE_POW)
				&& aCode->second().is< Number >() )
			{
				expr2 = aCode->first();
				exponent2 = aCode->second();
			}
		}

		AvmCode::iterator itArg = resMultArgs.begin();
		AvmCode::iterator endArg = resMultArgs.end();
		for( ; itArg != endArg ; ++itArg )
		{
			//case A * (B^<num>) + C + ...  with  B ^ <num>
			exponent1 = ExpressionConstant::INTEGER_ONE;
			expr1 = (*itArg);
			if( (*itArg).is< AvmCode >() )
			{
				aCode = (*itArg).to_ptr< AvmCode >();

				if( aCode->isOpCode(AVM_OPCODE_POW)
					&& aCode->second().is< Number >() )
				{
					expr1 = aCode->first();
					exponent1 = aCode->second();
				}
			}

			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				coef_sum = ExpressionConstructorNative::
						addNumber(exponent1, exponent2);
				if( coef_sum.isZero() )
				{
					itArg = resMultArgs.erase( itArg );
				}
				else
				{
					//==> A + B^(<num> + <num>) + C + ...
					(*itArg) = ExpressionConstructorNative::powExpr(
						expr1, coef_sum );
				}

				return( true );
			}
			else if( cmpResult > 0 )
			{
				resMultArgs.insert(itArg, term);

				return( true );
			}
		}

		resMultArgs.append( term );
	}

	return( true );
}


inline static bool multFlatExpr(const BF & term,
		AvmCode::this_container_type & resArgs,
		Numeric & resNumberCoef, bool & expandAddExpr)
{
	if( term.is< AvmCode >() )
	{
		AvmCode * argCode = term.to_ptr< AvmCode >();

		if( term.to_ptr< AvmCode >()->isOpCode(AVM_OPCODE_MULT) )
		{
			AvmCode::const_iterator itArg = argCode->begin();
			AvmCode::const_iterator endArg = argCode->end();
			for( ; itArg != endArg ; ++itArg )
			{
				if( (*itArg).isEqualZero() )
				{
					return( false );
				}
				else
				{
					multExpr(*itArg, resArgs, resNumberCoef, expandAddExpr);
				}
			}

			return( true );
		}
		else if( argCode->isOpCode(AVM_OPCODE_UMINUS) )
		{
			//==> numTerm := (- numTerm)
			resNumberCoef = ( - resNumberCoef );

			//==> A * C * ... * <expr>
			return( multExpr(argCode->first(), resArgs,
					resNumberCoef, expandAddExpr) );
		}
		else
		{
			return( multExpr(term, resArgs, resNumberCoef, expandAddExpr) );
		}
	}
	else
	{
		return( multExpr(term, resArgs, resNumberCoef, expandAddExpr) );
	}
}


inline static BF multCoefExpr(const Numeric & numCoef,
		BFCode & resCode, bool expandAddExpr)
{
	if( resCode->empty() || numCoef.isZero() )
	{
		return( numCoef );
	}
	else
	{
		if( expandAddExpr )
		{
			resCode->setOperator( OperatorManager::OPERATOR_PLUS );
		}

		if( numCoef.isOne() )
		{
			return( resCode->singleton() ? resCode->first() : resCode );
		}

		else if( expandAddExpr )
		{
			AvmCode::iterator itRes = resCode->begin();
			AvmCode::iterator endRes = resCode->end();
			for( ; itRes != endRes ; ++itRes )
			{
				(*itRes) = ExpressionConstructorNative::multExpr(numCoef, *itRes);
			}

			return( resCode );
		}
		else
		{
			return( ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_MULT,
					numCoef, resCode->getArgs()) );
		}
	}
}


BF ExpressionConstructorNative::multExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.is< Number >() )
	{
		if( arg0.to_ptr< Number >()->isZero() )
		{
			return( ExpressionConstant::INTEGER_ZERO );
		}
		else if( arg0.to_ptr< Number >()->isOne() )
		{
			return( arg1 );
		}

		if( arg1.is< Number >() )
		{
			if( arg1.to_ptr< Number >()->isZero() )
			{
				return( ExpressionConstant::INTEGER_ZERO );
			}
			else if( arg1.to_ptr< Number >()->isOne() )
			{
				return( arg0 );
			}

			return( ExpressionConstructor::newNumeric(
					Numeric::acquire( arg0.to_ptr< Number >() ).mult(
					Numeric::acquire( arg1.to_ptr< Number >() ) ) ) );
		}

		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_MULT, arg0, arg1) );
	}

	else if( arg1.is< Number >() )
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_MULT, arg1, arg0) );
	}

	else
	{
		BFCode resCode( OperatorManager::OPERATOR_MULT );

		Numeric numTerm = ExpressionConstant::INTEGER_ONE;
		bool expandAddExpr = false;

		if( multFlatExpr(arg0, resCode->getArgs(), numTerm, expandAddExpr) )
		{
			if( multFlatExpr(arg1, resCode->getArgs(), numTerm, expandAddExpr) )
			{
				return( multCoefExpr(numTerm, resCode, expandAddExpr) );
			}
		}

		return( ExpressionConstant::INTEGER_ZERO );
	}
}


BF ExpressionConstructorNative::multExpr(
		const AvmCode::this_container_type & listOfArg)
{
	BFCode resCode( OperatorManager::OPERATOR_MULT );

	Numeric numTerm = ExpressionConstant::INTEGER_ONE;
	bool expandAddExpr = false;

	AvmCode::const_iterator itArg = listOfArg.begin();
	AvmCode::const_iterator endArg = listOfArg.end();
	for( ; itArg != endArg ; ++itArg )
	{
		if( (*itArg).isEqualZero() )
		{
			return( ExpressionConstant::INTEGER_ZERO );
		}
		else if( not multFlatExpr(*itArg,
				resCode->getArgs(), numTerm, expandAddExpr) )
		{
			return( ExpressionConstant::INTEGER_ZERO );
		}
	}

	return( multCoefExpr(numTerm, resCode, expandAddExpr) );
}


////////////////////////////////////////////////////////////////////////////////
// POW EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::powExpr(const BF & arg0, const BF & arg1)
{
	if( arg1.is< Number >() )
	{
		if( arg1.to_ptr< Number >()->isZero() )
		{
			return( ExpressionConstant::INTEGER_ONE );
		}
		else if( arg1.to_ptr< Number >()->isOne() )
		{
			return( arg0 );
		}

		if( arg0.is< Number >() )
		{
			if( arg0.to_ptr< Number >()->isZero()
				|| arg0.to_ptr< Number >()->isOne() )
			{
				return( arg0 );
			}
			else if( arg1.to_ptr< Number >()->isUInteger() )
			{
				return( ExpressionConstructor::newNumeric(
						Numeric::acquire( arg0.to_ptr< Number >() ).pow(
						arg1.to_ptr< Number >()->toUInteger() ) ) );
			}
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_POW, arg0, arg1) );
}


////////////////////////////////////////////////////////////////////////////////
// DIV EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::divExpr(const BF & arg0, const BF & arg1)
{
	if( arg1.is< Number >() )
	{
		if( arg1.to_ptr< Number >()->isZero() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Division of " << arg0.str() << " by zero !!!"
					<< SEND_EXIT;

			return( BF::REF_NULL );
		}
		else if( arg1.to_ptr< Number >()->isOne() )
		{
			return( arg0 );
		}
		else if( arg0.is< Number >() )
		{
			if( arg0.to_ptr< Number >()->isZero() )
			{
				return( arg0 );
			}

			return( ExpressionConstructor::newNumeric(
					Numeric::acquire( arg0.to_ptr< Number >() ).div(
					Numeric::acquire( arg1.to_ptr< Number >() ) ) ) );
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_DIV, arg0, arg1) );
}


} /* namespace sep */
