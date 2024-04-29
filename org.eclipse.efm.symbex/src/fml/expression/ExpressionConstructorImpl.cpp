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
		AvmCode::OperandCollectionT & resArgs)
{
	if( resArgs.empty() )
	{
		resArgs.append( term );
	}
	else
	{
		int cmpResult;

		bool coef1;
		BF expr1;

		bool coef2 = true;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			const AvmCode & aCode = term.to< AvmCode >();

			if( aCode.isOpCode(AVM_OPCODE_NOT) )
			{
				coef2 = false;
				expr2 = aCode.first();
			}
		}

		AvmCode::const_iterator itOperand = resArgs.begin();
		AvmCode::const_iterator endOperand = resArgs.end();
		for( ; itOperand != endOperand ; ++itOperand )
		{
			//case A * (<sign> B) + C + ...  with  (<sign> B)
			coef1 = true;
			expr1 = (*itOperand);
			if( (*itOperand).is< AvmCode >() )
			{
				const AvmCode & aCode = (*itOperand).to< AvmCode >();

				if( aCode.isOpCode(AVM_OPCODE_NOT) )
				{
					coef1 = false;
					expr1 = aCode.first();
				}
			}

			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				return( coef1 == coef2 );
			}
			else if( cmpResult > 0 )
			{
				resArgs.insert(itOperand, term);

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
		AvmCode::OperandCollectionT & resArgs)
{
	if( term.is< AvmCode >() )
	{
		const AvmCode & termCode = term.to< AvmCode >();

		if( termCode.isOpCode(AVM_OPCODE_AND) )
		{
			for( const auto & itOperand : termCode.getOperands() )
			{
				if( itOperand.isEqualTrue() )
				{
					//continue;
				}
				else if( itOperand.isEqualFalse() )
				{
					return( false );
				}
				else if( not appendLogicTerm(itOperand, resArgs) )
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

		if( andFlatExpr(arg0, resCode->getOperands()) )
		{
			if( andFlatExpr(arg1, resCode->getOperands()) )
			{
				if( resCode->noOperand() )
				{
					return( ExpressionConstant::BOOLEAN_TRUE );
				}
				else
				{
					return( resCode->hasOneOperand() ?
							resCode->first() : resCode );
				}
			}
		}

		return( ExpressionConstant::BOOLEAN_FALSE );
	}
}


BF ExpressionConstructorNative::andExpr(
		const AvmCode::OperandCollectionT & operands)
{
	if( operands.nonempty() )
	{
		BFCode resCode( OperatorManager::OPERATOR_AND );

		for( const auto & itOperand : operands )
		{
			if( itOperand.isEqualTrue() )
			{
				//continue;
			}
			else if( itOperand.isEqualFalse() )
			{
				return( ExpressionConstant::BOOLEAN_FALSE );
			}
			else if( not andFlatExpr(itOperand, resCode->getOperands()) )
			{
				return( ExpressionConstant::BOOLEAN_FALSE );
			}
		}

		if( resCode->noOperand() )
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
		else
		{
			return( resCode->hasOneOperand() ? resCode->first() : resCode );
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
		AvmCode::OperandCollectionT & resArgs)
{
	if( term.is< AvmCode >() )
	{
		const AvmCode & argCode = term.to< AvmCode >();

		if( term.to< AvmCode >().isOpCode(AVM_OPCODE_OR) )
		{
			for( const auto & itOperand : argCode.getOperands() )
			{
				if( itOperand.isEqualTrue() )
				{
					return( false );
				}
				else if( itOperand.isEqualFalse() )
				{
					//continue;
				}
				else if( not appendLogicTerm(itOperand, resArgs) )
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

		if( orFlatExpr(arg0, resCode->getOperands()) )
		{
			if( orFlatExpr(arg1, resCode->getOperands()) )
			{
				if( resCode->noOperand() )
				{
					return( ExpressionConstant::BOOLEAN_TRUE );
				}
				else
				{
					return( resCode->hasOneOperand() ? resCode->first() : resCode );
				}
			}
		}

		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


BF ExpressionConstructorNative::orExpr(
		const AvmCode::OperandCollectionT & operands)
{
	if( operands.nonempty() )
	{
		BFCode resCode( OperatorManager::OPERATOR_OR );

		for( const auto & itOperand : operands )
		{
			if( itOperand.isEqualTrue() )
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
			else if( itOperand.isEqualFalse() )
			{
				//continue;
			}
			else if( not orFlatExpr(itOperand, resCode->getOperands()) )
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
		}

		if( resCode->noOperand() )
		{
			return( ExpressionConstant::BOOLEAN_FALSE);
		}
		else
		{
			return( resCode->hasOneOperand() ? resCode->first() : resCode );
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
// IMPLIES EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::impliesExpr(const BF & arg0, const BF & arg1)
{
//	return( ExpressionConstructor::newCode(
//			OperatorManager::OPERATOR_IMPLIES, arg0, arg1) );
	return( orExpr( notExpr(arg0), arg1) );
}


////////////////////////////////////////////////////////////////////////////////////
// QUANTIFIER EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::existsExpr(
		const BF & boundVar, const BF & formula)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_EXISTS, boundVar, formula) );
}

BF ExpressionConstructorNative::existsExpr(
		const AvmCode::OperandCollectionT & operands)
{
	return( ExpressionConstructor::newCode(
		OperatorManager::OPERATOR_EXISTS, operands) );
}


BF ExpressionConstructorNative::forallExpr(
		const BF & boundVar, const BF & formula)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_FORALL, boundVar, formula) );
}

BF ExpressionConstructorNative::forallExpr(
		const AvmCode::OperandCollectionT & operands)
{
	return( ExpressionConstructor::newCode(
		OperatorManager::OPERATOR_FORALL, operands) );
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
		const AvmCode & aCode = arg.to< AvmCode >();

		switch( aCode.getAvmOpCode() )
		{
			case AVM_OPCODE_EQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_NEQ, aCode.getOperands()) );
			}
			case AVM_OPCODE_NEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_EQ, aCode.getOperands()) );
			}

			case AVM_OPCODE_SEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_NSEQ, aCode.getOperands()) );
			}
			case AVM_OPCODE_NSEQ:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_SEQ, aCode.getOperands()) );
			}

			case AVM_OPCODE_LT:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_GTE, aCode.getOperands()) );
			}
			case AVM_OPCODE_LTE:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_GT, aCode.getOperands()) );
			}
			case AVM_OPCODE_GT:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_LTE, aCode.getOperands()) );
			}
			case AVM_OPCODE_GTE:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_LT, aCode.getOperands()) );
			}

			case AVM_OPCODE_NOT:
			{
				return( aCode.first() );
			}

			case AVM_OPCODE_AND:
			{
				BFCode resCode( OperatorManager::OPERATOR_OR );

				for( const auto & itOperand : aCode.getOperands() )
				{
					resCode->append( notExpr( itOperand ) );
				}

				return( resCode );
			}
			case AVM_OPCODE_NAND:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_AND, aCode.getOperands()) );
			}

//			case AVM_OPCODE_XAND:
//			{
//				return( ExpressionConstructor::newCode(
//						OperatorManager::OPERATOR_OR, aCode.getOperands()) );
//			}

			case AVM_OPCODE_OR:
			{
				BFCode resCode( OperatorManager::OPERATOR_AND );

				for( const auto & itOperand : aCode.getOperands() )
				{
					resCode->append( notExpr( itOperand ) );
				}

				return( resCode );
			}
			case AVM_OPCODE_NOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_OR, aCode.getOperands()) );
			}

			case AVM_OPCODE_XOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_XNOR, aCode.getOperands()) );
			}
			case AVM_OPCODE_XNOR:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_XOR, aCode.getOperands()) );
			}

			case AVM_OPCODE_IMPLIES:
			{
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_AND,
						aCode.first() , notExpr( aCode.second() ) ));
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


////////////////////////////////////////////////////////////////////////////
// BITWISE EXPRESSION
////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::bandExpr(const BF & arg0, const BF & arg1)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_BAND, arg0, arg1) );
}

BF ExpressionConstructorNative::borExpr(const BF & arg0, const BF & arg1)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_BOR, arg0, arg1) );
}

BF ExpressionConstructorNative::bxorExpr(const BF & arg0, const BF & arg1)
{
	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_BXOR, arg0, arg1) );
}

BF ExpressionConstructorNative::bnotExpr(const BF & arg)
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
				OperatorManager::OPERATOR_BNOT, arg) );
	}
}


////////////////////////////////////////////////////////////////////////////////////
// COMPARE EXPRESSION
////////////////////////////////////////////////////////////////////////////////////

template< typename OP_T > BF compare(
		const BF & lhArg, const BF & rhArg, const Operator * cmpOp, OP_T cmp)
{
	//case X rel_op Y  ==> diff := X - Y
	BF diff = ExpressionConstructorNative::minusExpr(lhArg, rhArg);

	//case diff = <num>
	if( diff.is< Number >() )
	{
		return( ExpressionConstructorNative::newBoolean(
				cmp(diff.to< Number >().sign(), 0) ) );
	}

	//case diff = <term>
	else if( diff.is< AvmCode >() )
	{
		const AvmCode & diffCode = diff.to< AvmCode >();

		//case diff = A + B + ...
		if( diffCode.isOpCode(AVM_OPCODE_PLUS) )
		{
			BFCode lhCode( OperatorManager::OPERATOR_PLUS );
			BFCode rhCode( OperatorManager::OPERATOR_PLUS );

			for( const auto & itOperand : diffCode.getOperands() )
			{
				//case diff = A + B + ... + <num>
				if( itOperand.is< Number >() )
				{
					rhCode->append( ExpressionConstructorNative::
							uminusExpr( itOperand ) );
				}

				else if( itOperand.is< AvmCode >() )
				{
					const AvmCode & argCode = itOperand.to< AvmCode >();

					//case diff = (- A) + B + C +...
					if( argCode.isOpCode(AVM_OPCODE_UMINUS) )
					{
						rhCode->append( argCode.first() );
					}
					//case diff = (- <num> * X * Y * ...) + A + B + ...
					else if( argCode.isOpCode(AVM_OPCODE_MULT)
							&& argCode.first().is< Number >()
							&& argCode.first().to<
									Number >().strictlyNegative() )
					{
						rhCode->append( ExpressionConstructorNative::
								uminusExpr( itOperand ) );
					}
					else
					{
						lhCode->append( itOperand );
					}
				}
				else
				{
					lhCode->append( itOperand );
				}
			}

			BFCode cmpCode( cmpOp );

			if( lhCode->hasOneOperand() )
			{
				cmpCode->append( lhCode->first() );
			}
			else if( lhCode->hasManyOperands() )
			{
				cmpCode->append( lhCode );
			}
			else
			{
				cmpCode->append( ExpressionConstant::INTEGER_ZERO );
			}

			if( rhCode->hasOneOperand() )
			{
				cmpCode->append( rhCode->first() );
			}
			else if( rhCode->hasManyOperands() )
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
		if( num0.to< Number >().isZero() )
		{
			return( num1 );
		}
		else if( num1.is< Number >() )
		{
			if( num1.to< Number >().isZero() )
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
		if( num1.to< Number >().isZero() )
		{
			return( num0 );
		}
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_PLUS, num0, num1) );
}


static void addExpr(const BF & term,
		AvmCode::OperandCollectionT & resArgs, Numeric & resNumberArg)
{
	if( term.is< Number >() )
	{
		resNumberArg = resNumberArg + term;
	}
	else if( resArgs.empty() )
	{
		resArgs.append( term );
	}
	else
	{
		Numeric coef_sum;

		int cmpResult;

		Numeric coef1;
		BF expr1;

		Numeric coef2 = ExpressionConstant::INTEGER_ONE;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			const AvmCode & aCode = term.to< AvmCode >();

			if( aCode.isOpCode(AVM_OPCODE_MULT)
				&& aCode.first().is< Number >() )
			{
				coef2 = aCode.first();
				if( aCode.size() == 2 )
				{
					expr2 = aCode.second();
				}
				else
				{
					expr2 = ExpressionConstructor::newCodeTail(
							OperatorManager::OPERATOR_MULT, aCode.getOperands());
				}
			}
			else if( aCode.isOpCode(AVM_OPCODE_UMINUS) )
			{
				coef2 = ExpressionConstant::INTEGER_MINUS_ONE;
				expr2 = aCode.first();
			}
		}

		AvmCode::iterator itOperand = resArgs.begin();
		AvmCode::iterator endOperand = resArgs.end();
		for( ; itOperand != endOperand ; ++itOperand )
		{
			//case A + (<num>*B) + C + ... with  <num> * B
			coef1 = ExpressionConstant::INTEGER_ONE;
			expr1 = (*itOperand);
			if( (*itOperand).is< AvmCode >() )
			{
				const AvmCode & aCode = (*itOperand).to< AvmCode >();

				if( aCode.isOpCode(AVM_OPCODE_MULT)
					&& aCode.first().is< Number >() )
				{
					coef1 = aCode.first();
					if( aCode.size() == 2 )
					{
						expr1 = aCode.second();
					}
					else
					{
						expr1 = ExpressionConstructor::newCodeTail(
								OperatorManager::OPERATOR_MULT,
								aCode.getOperands());
					}
				}
				else if( aCode.isOpCode(AVM_OPCODE_UMINUS) )
				{
					coef1 = ExpressionConstant::INTEGER_MINUS_ONE;
					expr1 = aCode.first();
				}
			}

			//==> A + (<num> + <num>)*B + C + ...
			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				coef_sum = ExpressionConstructorNative::addNumber(coef1, coef2);
				if( coef_sum.isZero() )
				{
					itOperand = resArgs.erase( itOperand );
				}
				else
				{
					(*itOperand) = ExpressionConstructorNative::multExpr(
							coef_sum, expr1);
				}

				return;
			}
			else if( cmpResult > 0 )
			{
				resArgs.insert(itOperand, term);

				return;
			}
		}

		resArgs.append( term );
	}
}


inline static void addFlatExpr(const BF & term,
		AvmCode::OperandCollectionT & resArgs, Numeric & resNumberArg)
{
	if( term.is< AvmCode >() )
	{
		const AvmCode & termCode = term.to< AvmCode >();

		if( termCode.isOpCode(AVM_OPCODE_PLUS) )
		{
			for( const auto & itOperand : termCode.getOperands() )
			{
				addExpr(itOperand, resArgs, resNumberArg);
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

		addFlatExpr(arg0, resCode->getOperands(), numTerm);

		addFlatExpr(arg1, resCode->getOperands(), numTerm);

		if( resCode->noOperand() )
		{
			return( numTerm );
		}
		else if( not numTerm.isZero() )
		{
			resCode->append( numTerm );
		}

		return( resCode->hasOneOperand() ? resCode->first() : resCode );
	}
}


BF ExpressionConstructorNative::addExpr(
		const AvmCode::OperandCollectionT & operands)
{
	BFCode resCode( OperatorManager::OPERATOR_PLUS );

	Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

	for( const auto & itOperand : operands )
	{
		addFlatExpr(itOperand, resCode->getOperands(), numTerm);
	}

	if( resCode->noOperand() )
	{
		return( numTerm );
	}
	else if( not numTerm.isZero() )
	{
		resCode->append( numTerm );
	}

	return( resCode->hasOneOperand() ? resCode->first() : resCode );
}



////////////////////////////////////////////////////////////////////////////////
// MINUS EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::minusExpr(
		const AvmCode::OperandCollectionT & operands)
{
	if( operands.singleton() )
	{
		return( operands.first() );
	}
	else if( operands.populated() )
	{
		AvmCode::OperandCollectionT addArgs;

		AvmCode::const_iterator itOperand = operands.begin();
		AvmCode::const_iterator endOperand = operands.end();
		addArgs.append(*itOperand);
		for( ++itOperand ; itOperand != endOperand ; ++itOperand )
		{
			addArgs.append( uminusExpr(*itOperand) );
		}

		return( addExpr( addArgs ) );
	}
	else
	{
		return( newExpr( static_cast< avm_integer_t >(0L) ) );
	}
}

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
//			res.to< Integer >().uminus();
//
//			return( res );
//		}
//
//		//case - <rational>
//		case FORM_BUILTIN_RATIONAL_KIND:
//		{
//			BF res = arg;
//			res.makeWritable();
//			res.to< Rational >().uminus();
//
//			return( res );
//		}
//
//		//case - <float>
//		case FORM_BUILTIN_FLOAT_KIND:
//		{
//			BF res = arg;
//			res.makeWritable();
//			res.to< Float >().uminus();
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
		const AvmCode & aCode = arg.to< AvmCode >();

		switch( aCode.getAvmOpCode() )
		{
			//case - (A + B + ...)
			case AVM_OPCODE_PLUS:
			{
				BFCode resCode( OperatorManager::OPERATOR_PLUS );

				for( const auto & itOperand : aCode.getOperands() )
				{
					resCode->append( uminusExpr( itOperand ) );
				}

				return( resCode );
			}

			//case - (A - B - ...)
			case AVM_OPCODE_MINUS:
			{
				AvmCode::const_iterator itOperand = aCode.begin();

				BFCode resCode( OperatorManager::OPERATOR_PLUS,
						uminusExpr( *itOperand ) );

				AvmCode::const_iterator endOperand = aCode.end();
				for( ++itOperand ; itOperand != endOperand ; ++itOperand )
				{
					resCode->append( *itOperand );
				}

				return( resCode );
			}

			//case - (- <term>)
			case AVM_OPCODE_UMINUS:
			{
				return( aCode.first() );
			}

			//case - (A * B * ...)
			case AVM_OPCODE_MULT:
			{
				//case +- (<num> * A * B * ...)
				if( aCode.first().is< Number >() )
				{
					AvmCode::const_iterator itOperand = aCode.begin();

					BFCode resCode( OperatorManager::OPERATOR_MULT );

					if( not (*itOperand).to< Number >().isNegativeOne() )
					{
						resCode->append( uminusExpr( *itOperand ) );
					}

					AvmCode::const_iterator endOperand = aCode.end();
					for( ++itOperand ; itOperand != endOperand ; ++itOperand )
					{
						resCode->append( *itOperand );
					}

					//==> (- <num>) * A * B * ...
					return( resCode );
				}

				//==> (- 1) * A * B * ...
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_MULT ,
						ExpressionConstant::INTEGER_MINUS_ONE,
						aCode.getOperands()) );
			}

			//case - (A / B )
			case AVM_OPCODE_DIV:
			{
				//==> ((- 1) * A) / B
				return( ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_DIV ,
						uminusExpr( aCode.first() ), aCode.second()) );
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
		AvmCode::OperandCollectionT & resMultArgs,
		Numeric & resNumberCoef, bool & expandAddExpr)
{
	if( resNumberCoef.isZero() )
	{
		return( false );
	}
	else if( term.is< Number >() )
	{
		if( term.to< Number >().isZero() )
		{
			resNumberCoef = ExpressionConstant::INTEGER_ZERO;

			return( false );
		}
		else
		{
			resNumberCoef = resNumberCoef * term;
		}
	}
	else if( resMultArgs.empty() )
	{
		if( term.is< AvmCode >() &&
			term.to< AvmCode >().isOpCode(AVM_OPCODE_PLUS) )
		{
			resMultArgs.append( term.to< AvmCode >().getOperands() );

			expandAddExpr = true;
		}
		else
		{
			resMultArgs.append( term );
		}
	}
	else if( expandAddExpr )
	{
		AvmCode::OperandCollectionT resAddArgs( resMultArgs );
		resMultArgs.clear();

		Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

		for( const auto & itOperand : resAddArgs )
		{
			addFlatExpr(
					ExpressionConstructorNative::multExpr(term, itOperand),
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
			term.to< AvmCode >().isOpCode(AVM_OPCODE_PLUS) )
	{
		BF multArg = resMultArgs.singleton() ? resMultArgs.first() :
				ExpressionConstructor::newCode(
						OperatorManager::OPERATOR_MULT, resMultArgs);

		resMultArgs.clear();
		Numeric numTerm = ExpressionConstant::INTEGER_ZERO;

		for( const auto & itOperand : term.to< AvmCode >().getOperands() )
		{
			addFlatExpr(
					ExpressionConstructorNative::multExpr(multArg, itOperand),
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
		Numeric coef_sum;

		int cmpResult;

		Numeric exponent1;
		BF expr1;

		Numeric exponent2 = ExpressionConstant::INTEGER_ONE;
		BF expr2 = term;
		if( term.is< AvmCode >() )
		{
			const AvmCode & aCode = term.to< AvmCode >();

			if( aCode.isOpCode(AVM_OPCODE_POW)
				&& aCode.second().is< Number >() )
			{
				expr2 = aCode.first();
				exponent2 = aCode.second();
			}
		}

		AvmCode::iterator itOperand = resMultArgs.begin();
		AvmCode::iterator endOperand = resMultArgs.end();
		for( ; itOperand != endOperand ; ++itOperand )
		{
			//case A * (B^<num>) + C + ...  with  B ^ <num>
			exponent1 = ExpressionConstant::INTEGER_ONE;
			expr1 = (*itOperand);
			if( (*itOperand).is< AvmCode >() )
			{
				const AvmCode & aCode = (*itOperand).to< AvmCode >();

				if( aCode.isOpCode(AVM_OPCODE_POW)
					&& aCode.second().is< Number >() )
				{
					expr1 = aCode.first();
					exponent1 = aCode.second();
				}
			}

			if( (cmpResult = expr1.compare( expr2 )) == 0 )
			{
				coef_sum = ExpressionConstructorNative::
						addNumber(exponent1, exponent2);
				if( coef_sum.isZero() )
				{
					itOperand = resMultArgs.erase( itOperand );
				}
				else
				{
					//==> A + B^(<num> + <num>) + C + ...
					(*itOperand) = ExpressionConstructorNative::powExpr(
						expr1, coef_sum );
				}

				return( true );
			}
			else if( cmpResult > 0 )
			{
				resMultArgs.insert(itOperand, term);

				return( true );
			}
		}

		resMultArgs.append( term );
	}

	return( true );
}


inline static bool multFlatExpr(const BF & term,
		AvmCode::OperandCollectionT & resArgs,
		Numeric & resNumberCoef, bool & expandAddExpr)
{
	if( term.is< AvmCode >() )
	{
		const AvmCode & termCode = term.to< AvmCode >();

		if( termCode.isOpCode(AVM_OPCODE_MULT) )
		{
			for( const auto & itOperand : termCode.getOperands() )
			{
				if( itOperand.isEqualZero() )
				{
					return( false );
				}
				else
				{
					multExpr(itOperand, resArgs, resNumberCoef, expandAddExpr);
				}
			}

			return( true );
		}
		else if( termCode.isOpCode(AVM_OPCODE_UMINUS) )
		{
			//==> numTerm := (- numTerm)
			resNumberCoef = ( - resNumberCoef );

			//==> A * C * ... * <expr>
			return( multExpr(termCode.first(), resArgs,
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
	if( resCode->noOperand() || numCoef.isZero() )
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
			return( resCode->hasOneOperand() ? resCode->first() : resCode );
		}

		else if( expandAddExpr )
		{
			for( auto & itOperand : resCode->getOperands() )
			{
				if( itOperand.is< AvmCode >() )
				{
					const AvmCode & aCode = itOperand.to< AvmCode >();

					if( aCode.isOpCode(AVM_OPCODE_MULT)
						&& aCode.first().is< Number >() )
					{
						itOperand = ExpressionConstructor::newCodeTail(
								OperatorManager::OPERATOR_MULT,
								ExpressionConstructorNative::
										multExpr(numCoef, aCode.first()),
								aCode.getOperands());
					}
					else
					{
						itOperand = ExpressionConstructorNative::
								multExpr(numCoef, itOperand);
					}
				}
				else
				{
					itOperand = ExpressionConstructorNative::
							multExpr(numCoef, itOperand);
				}
			}

			return( resCode );
		}
		else
		{
			return( ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_MULT,
					numCoef, resCode->getOperands()) );
		}
	}
}


BF ExpressionConstructorNative::multExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.is< Number >() )
	{
		if( arg0.to< Number >().isZero() )
		{
			return( ExpressionConstant::INTEGER_ZERO );
		}
		else if( arg0.to< Number >().isOne() )
		{
			return( arg1 );
		}

		if( arg1.is< Number >() )
		{
			if( arg1.to< Number >().isZero() )
			{
				return( ExpressionConstant::INTEGER_ZERO );
			}
			else if( arg1.to< Number >().isOne() )
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

		if( multFlatExpr(arg0, resCode->getOperands(), numTerm, expandAddExpr) )
		{
			if( multFlatExpr(arg1, resCode->getOperands(), numTerm, expandAddExpr) )
			{
				return( multCoefExpr(numTerm, resCode, expandAddExpr) );
			}
		}

		return( ExpressionConstant::INTEGER_ZERO );
	}
}


BF ExpressionConstructorNative::multExpr(
		const AvmCode::OperandCollectionT & operands)
{
	BFCode resCode( OperatorManager::OPERATOR_MULT );

	Numeric numTerm = ExpressionConstant::INTEGER_ONE;
	bool expandAddExpr = false;

	for( const auto & itOperand : operands )
	{
		if( itOperand.isEqualZero() )
		{
			return( ExpressionConstant::INTEGER_ZERO );
		}
		else if( not multFlatExpr(itOperand,
				resCode->getOperands(), numTerm, expandAddExpr) )
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
		if( arg1.to< Number >().isZero() )
		{
			return( ExpressionConstant::INTEGER_ONE );
		}
		else if( arg1.to< Number >().isOne() )
		{
			return( arg0 );
		}

		if( arg0.is< Number >() )
		{
			if( arg0.to< Number >().isZero()
				|| arg0.to< Number >().isOne() )
			{
				return( arg0 );
			}
			else if( arg1.to< Number >().isUInteger() )
			{
				return( ExpressionConstructor::newNumeric(
						Numeric::acquire( arg0.to_ptr< Number >() ).pow(
						arg1.to< Number >().toUInteger() ) ) );
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
		if( arg1.to< Number >().isZero() )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Division of " << arg0.str() << " by zero !!!"
					<< SEND_EXIT;

//			return( BF::REF_NULL );
			return( ExpressionConstant::INTEGER_42 );
		}
		else if( arg1.to< Number >().isOne() )
		{
			return( arg0 );
		}
		else if( arg0.is< Number >() )
		{
			if( arg0.to< Number >().isZero() )
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


////////////////////////////////////////////////////////////////////////////////
// MOD EXPRESSION
////////////////////////////////////////////////////////////////////////////////

BF ExpressionConstructorNative::modExpr(const BF & arg0, const BF & arg1)
{
	if( arg0.is< Integer >() && arg1.is< Integer >() )
	{
		return( ExpressionConstructor::newNumeric(
				Numeric::acquire( arg0.to_ptr< Number >() ).mod(
				Numeric::acquire( arg1.to_ptr< Number >() ) ) ) );
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MOD, arg0, arg1) );
}



} /* namespace sep */
