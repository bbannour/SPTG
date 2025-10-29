/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 déc. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionEval.h"

#include <fml/executable/ExecutableLib.h>

#include <fml/expression/AvmCode.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


BF ExpressionEval::value(const BFCode & aCode, bool destroy_arg)
{
	switch( aCode.getAvmOpCode() )
	{
		case AVM_OPCODE_RANDOM:
		{
			return( ExpressionEval::random(aCode->first()) );
		}

		case AVM_OPCODE_ABS:
		{
			return( ExpressionEval::abs(aCode->first()) );
		}
		case AVM_OPCODE_CEIL:
		{
			return( ExpressionEval::ceil(aCode->first()) );
		}
		case AVM_OPCODE_FLOOR:
		{
			return( ExpressionEval::floor(aCode->first()) );
		}
		case AVM_OPCODE_ROUND:
		{
			return( ExpressionEval::round(aCode->first()) );
		}
		case AVM_OPCODE_TRUNCATE:
		{
			return( ExpressionEval::truncate(aCode->first()) );
		}


		case AVM_OPCODE_MIN:
		{
			return( ExpressionEval::min(aCode) );
		}
		case AVM_OPCODE_MAX:
		{
			return( ExpressionEval::max(aCode) );
		}


		case AVM_OPCODE_MOD:
		{
			return( ExpressionEval::mod(aCode->first(),
					aCode->second()) );
		}

		case AVM_OPCODE_SQRT:
		{
			return( ExpressionEval::sqrt(aCode->first()) );
		}

		case AVM_OPCODE_EXP:
		{
			return( ExpressionEval::exp(aCode->first()) );
		}
		case AVM_OPCODE_LN:
		{
			return( ExpressionEval::ln(aCode->first()) );
		}
		case AVM_OPCODE_LOG:
		{
			return( ExpressionEval::log(aCode->first()) );
		}

		case AVM_OPCODE_SIN:
		{
			return( ExpressionEval::sin(aCode->first()) );
		}
		case AVM_OPCODE_COS:
		{
			return( ExpressionEval::cos(aCode->first()) );
		}
		case AVM_OPCODE_TAN:
		{
			return( ExpressionEval::tan(aCode->first()) );
		}

		case AVM_OPCODE_SINH:
		{
			return( ExpressionEval::sinh(aCode->first()) );
		}
		case AVM_OPCODE_COSH:
		{
			return( ExpressionEval::cosh(aCode->first()) );
		}
		case AVM_OPCODE_TANH:
		{
			return( ExpressionEval::tanh(aCode->first()) );
		}

		case AVM_OPCODE_ASIN:
		{
			return( ExpressionEval::asin(aCode->first()) );
		}
		case AVM_OPCODE_ACOS:
		{
			return( ExpressionEval::acos(aCode->first()) );
		}
		case AVM_OPCODE_ATAN:
		{
			return( ExpressionEval::atan(aCode->first()) );
		}
		case AVM_OPCODE_ATAN2:
		{
			return( ExpressionEval::atan2(aCode->first(),
					aCode->second()) );
		}

		case AVM_OPCODE_ASINH:
		{
			return( ExpressionEval::asinh(aCode->first()) );
		}
		case AVM_OPCODE_ACOSH:
		{
			return( ExpressionEval::acosh(aCode->first()) );
		}
		case AVM_OPCODE_ATANH:
		{
			return( ExpressionEval::atanh(aCode->first()) );
		}


		default:
		{
			return( aCode );
		}
	}
}


BF ExpressionEval::random(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_RANDOM, aCode) );
}


BF ExpressionEval::abs(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ABS, aCode) );
}


BF ExpressionEval::ceil(const BF & aCode)
{
	if( aCode.isInteger() )
	{
		return( aCode );
	}

	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_CEIL, aCode) );
}


BF ExpressionEval::floor(const BF & aCode)
{
	if( aCode.isInteger() )
	{
		return( aCode );
	}

	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_FLOOR, aCode) );
}


BF ExpressionEval::round(const BF & aCode)
{
	if( aCode.isInteger() )
	{
		return( aCode );
	}

	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ROUND, aCode) );
}


BF ExpressionEval::truncate(const BF & aCode)
{
	if( aCode.isInteger() )
	{
		return( aCode );
	}

	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_TRUNCATE, aCode) );
}


BF ExpressionEval::min(const BF & aCode1, const BF & aCode2)
{
	if( aCode1 == ExecutableLib::_INFINITY_ )
	{
		return( aCode2 );
	}
	else if( aCode2 == ExecutableLib::_INFINITY_ )
	{
		return( aCode1 );
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MIN, aCode1, aCode2) );
}


BF ExpressionEval::max(const BF & aCode1, const BF & aCode2)
{
	if( aCode1 == ExecutableLib::_INFINITY_ )
	{
		return( aCode1 );
	}
	else if( aCode2 == ExecutableLib::_INFINITY_ )
	{
		return( aCode2 );
	}

	return( ExpressionConstructor::newCode(
			OperatorManager::OPERATOR_MAX, aCode1, aCode2) );
}



BF ExpressionEval::min(const BFCode & aCode)
{
	AvmCode::size_type argCount = aCode->size();

	if( argCount > 2 )
	{
		BFList symbolicValue;
		BF minValue;

		AvmCode::const_iterator itOperand = aCode->begin();
		AvmCode::const_iterator endOperand = aCode->end();
		for( ; itOperand != endOperand ; ++itOperand )
		{
			if ( (*itOperand).isNumeric() )
			{
				minValue = (*itOperand);

				// NEXT
				++itOperand;

				break;
			}
			else if( (*itOperand) != ExecutableLib::_INFINITY_ )
			{
				symbolicValue.add_unique( (*itOperand) );
			}
		}

		for( ; itOperand != endOperand ; ++itOperand )
		{
			if( (*itOperand) == ExecutableLib::_INFINITY_ )
			{
//				continue;
			}

			else if ( (*itOperand).isNumeric() )
			{
				minValue = ExpressionEval::min(minValue, *itOperand);
			}
			else
			{
				symbolicValue.add_unique( (*itOperand) );
			}
		}

		if( symbolicValue.nonempty() )
		{
			BFCode newCode(OperatorManager::OPERATOR_MIN);
			if( minValue.valid() )
			{
				newCode->append( minValue );
			}
			newCode->append( symbolicValue );

			return( newCode );
		}
		else if( minValue.valid() )
		{
			return( minValue );
		}
		else if( aCode->hasOperand() )
		{
			return( aCode->first() );
		}
		else
		{
			return( aCode );
		}
	}
	else if( argCount == 2 )
	{
		return( ExpressionEval::min(aCode->first(), aCode->second()) );
	}
	else if( argCount == 1 )
	{
		return( aCode->first() );
	}
	else
	{
		return( aCode );
	}
}

BF ExpressionEval::max(const BFCode & aCode)
{
	AvmCode::size_type argCount = aCode->size();

	if( argCount > 2 )
	{
		BFList symbolicValue;
		BF maxValue;

		AvmCode::const_iterator itOperand = aCode->begin();
		AvmCode::const_iterator endOperand = aCode->end();
		for( ; itOperand != endOperand ; ++itOperand )
		{
			if( (*itOperand) == ExecutableLib::_INFINITY_ )
			{
				return( *itOperand );
			}

			else if ( (*itOperand).isNumeric() )
			{
				maxValue = (*itOperand);

				// NEXT
				++itOperand;

				break;
			}
			else
			{
				symbolicValue.add_unique( (*itOperand) );
			}
		}

		for( ; itOperand != endOperand ; ++itOperand )
		{
			if( (*itOperand) == ExecutableLib::_INFINITY_ )
			{
				return( (*itOperand) );
			}

			else if ( (*itOperand).isNumeric() )
			{
				maxValue = ExpressionEval::max(maxValue, *itOperand);
			}
			else
			{
				symbolicValue.add_unique( (*itOperand) );
			}
		}

		if( symbolicValue.nonempty() )
		{
			BFCode newCode(OperatorManager::OPERATOR_MAX);
			if( maxValue.valid() )
			{
				newCode->append( maxValue );
			}
			newCode->append( symbolicValue );

			return( newCode );
		}
		else if( maxValue.valid() )
		{
			return( maxValue );
		}
		else if( aCode->hasOperand() )
		{
			return( aCode->first() );
		}
		else
		{
			return( aCode );
		}
	}
	else if( argCount == 2 )
	{
		return( ExpressionEval::max(aCode->first(), aCode->second()) );
	}
	else if( argCount == 1 )
	{
		return( aCode->first() );
	}
	else
	{
		return( aCode );
	}
}



BF ExpressionEval::mod(const BF & aCode1, const BF & aCode2)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_MOD, aCode1, aCode2) );
}




BF ExpressionEval::sqrt(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_SQRT, aCode) );
}


BF ExpressionEval::exp(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_EXP, aCode) );
}


BF ExpressionEval::ln(const BF & aCode)
{
	switch( aCode.classKind() )
	{
		case FORM_BUILTIN_INTEGER_KIND:
		{
			if( aCode.to< Integer >().toInteger() > 0 )
			{
//				return( ExpressionConstructor::newFloat(
//						::ln(aCode.to< Integer >().toInteger())) );
			}
			break;
		}

		case FORM_BUILTIN_FLOAT_KIND:
		{
			if( aCode.toFloat() > 0 )
			{
//				return( ExpressionConstructor::newFloat(
//						::ln(aCode.toFloat())) );
			}
			break;
		}


		default:
		{
			break;
		}
	}

	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_LN, aCode) );
}


BF ExpressionEval::log(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_LOG, aCode) );
}




BF ExpressionEval::sin(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_SIN, aCode) );
}

BF ExpressionEval::cos(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_COS, aCode) );
}

BF ExpressionEval::tan(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_TAN, aCode) );
}





BF ExpressionEval::sinh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_SINH, aCode) );
}

BF ExpressionEval::cosh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_COSH, aCode) );
}

BF ExpressionEval::tanh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_TANH, aCode) );
}



BF ExpressionEval::asin(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ASIN, aCode) );
}

BF ExpressionEval::acos(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ACOS, aCode) );
}

BF ExpressionEval::atan(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ATAN, aCode) );
}


BF ExpressionEval::atan2(const BF & aCode1, const BF & aCode2)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ATAN2, aCode1, aCode2) );
}



BF ExpressionEval::asinh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ASINH, aCode) );
}

BF ExpressionEval::acosh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ACOSH, aCode) );
}

BF ExpressionEval::atanh(const BF & aCode)
{
	return( ExpressionConstructor::newExpr(
			OperatorManager::OPERATOR_ATANH, aCode) );
}



}
