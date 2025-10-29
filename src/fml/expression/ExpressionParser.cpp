/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 03 avr. 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionParser.h"

#include <common/GeneralException.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/infrastructure/Machine.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{

/**
 * PARSER EXPRESSION RULES
 */

BF ExpressionParser::parseExpression()
{
	return assignExpression();
}

BF ExpressionParser::assignExpression()
{
	BF bfValue = conditionalExpression();
//	( relationalOp();
	if (next_token_is(Token::T_ASSIGN))
	{
		return ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_ASSIGN, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_ADD_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_PLUS, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_SUB_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MINUS, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_MULT_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MULT, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_DIV_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_DIV, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_POW_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_POW, bfValue, parseExpression());
	}
	else if (next_token_is(Token::T_MOD_ASSIGN))
	{
		return ExpressionConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MOD, bfValue, parseExpression());
	}
//	)?
	return bfValue;
}

BF ExpressionParser::conditionalExpression()
{
	BF bfValue = conditionalOrExpression();

	if (next_token_is(Token::T_TERNARY))
	{
//		( QUESTION
		BF bfThen = parseExpression();
//		COLON
		if (next_token_is(Token::T_COLON))
		{
			return( ExpressionConstructor::newCode(
					OperatorManager::OPERATOR_IFE,
					bfValue, bfThen, parseExpression()) );
		}
//		)?
		else
		{
			throw DiversityError( "Expected token< ':' > for conditional ;? expression recognition !" );
		}
	}

	return bfValue;
}

BF ExpressionParser::conditionalOrExpression()
{
	BF bfValue = conditionalAndExpression();
//	( LOR
	while (next_token_is(Token::T_LOR) || next_token_symbol_is("or"))
	{
		bfValue = ExpressionConstructor::orExpr(
				bfValue, conditionalAndExpression());
	}
//	)*
	return bfValue;
}

BF ExpressionParser::conditionalAndExpression()
{
	BF bfValue = bitwiseOrExpression();
//	( LAND
	while (next_token_is(Token::T_LAND) || next_token_symbol_is("and"))
	{
		bfValue = ExpressionConstructor::andExpr(
				bfValue, bitwiseOrExpression());
	}
//	)*
	return bfValue;
}

BF ExpressionParser::bitwiseOrExpression()
{
	BF bfValue = bitwiseXorExpression();
//	( BOR
	while (next_token_is(Token::T_BOR))
	{
		bfValue = ExpressionConstructor::borExpr(
				bfValue, bitwiseXorExpression());
	}
//	)*
	return bfValue;
}

BF ExpressionParser::bitwiseXorExpression()
{
	BF bfValue = bitwiseAndExpression();
//	( BXOR
	while (next_token_is(Token::T_BXOR) || next_token_symbol_is("xor"))
	{
		bfValue = ExpressionConstructor::bxorExpr(
				bfValue, bitwiseAndExpression());
	}
//	)*
	return bfValue;
}

BF ExpressionParser::bitwiseAndExpression()
{
	BF bfValue = equalityExpression();
//	( BAND
	while (next_token_is(Token::T_BAND))
	{
		bfValue = ExpressionConstructor::bandExpr(
				bfValue, equalityExpression());
	}
//	)*
	return bfValue;
}


BF ExpressionParser::equalityExpression()
{
	BF bfValue = relationalExpression();
//	( equalOp();
	if (next_token_is(Token::T_EQ))
	{
		return ExpressionConstructor::eqExpr(bfValue, relationalExpression());
	}
	else if (next_token_is(Token::T_NEQ))
	{
		return ExpressionConstructor::neqExpr(bfValue, relationalExpression());
	}
	else if (next_token_is(Token::T_SEQ))
	{
		return ExpressionConstructor::seqExpr(bfValue, relationalExpression());
	}
	else if (next_token_is(Token::T_NSEQ))
	{
		return ExpressionConstructor::nseqExpr(bfValue, relationalExpression());
	}
//	)?
	return bfValue;
}

Operator * ExpressionParser::equalOp()
{
	if (next_token_is(Token::T_EQ))
	{
		return OperatorManager::OPERATOR_EQ;
	}
	else if (next_token_is(Token::T_NEQ))
	{
		return OperatorManager::OPERATOR_NEQ;
	}
	else if (next_token_is(Token::T_SEQ))
	{
		return OperatorManager::OPERATOR_SEQ;
	}
	else if (next_token_is(Token::T_NSEQ))
	{
		return OperatorManager::OPERATOR_NSEQ;
	}

	return OperatorManager::OPERATOR_NULL;
}


BF ExpressionParser::relationalExpression()
{
	BF bfValue = shiftExpression();
//	( relationalOp();
	if (next_token_is(Token::T_LT))
	{
		return ExpressionConstructor::ltExpr(bfValue, shiftExpression());
	}
	else if (next_token_is(Token::T_LTE))
	{
		return ExpressionConstructor::lteExpr(bfValue, shiftExpression());
	}
	else if (next_token_is(Token::T_GT))
	{
		return ExpressionConstructor::gtExpr(bfValue, shiftExpression());
	}
	else if (next_token_is(Token::T_GTE))
	{
		return ExpressionConstructor::gteExpr(bfValue, shiftExpression());
	}
//	)?
	return bfValue;
}

Operator * ExpressionParser::relationalOp()
{
	if (next_token_is(Token::T_LT))
	{
		return OperatorManager::OPERATOR_LT;
	}
	else if (next_token_is(Token::T_LTE))
	{
		return OperatorManager::OPERATOR_LTE;
	}
	else if (next_token_is(Token::T_GT))
	{
		return OperatorManager::OPERATOR_GT;
	}
	else if (next_token_is(Token::T_GTE))
	{
		return OperatorManager::OPERATOR_GTE;
	}

	return OperatorManager::OPERATOR_NULL;
}


BF ExpressionParser::shiftExpression()
{
	BF bfValue = additiveExpression();
//	(
	shiftOp();
	if (next_token_is(Token::T_LSHIFT))
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_LSHIFT,
				bfValue, additiveExpression()) );
	}
	else if (next_token_is(Token::T_RSHIFT))
	{
		return( ExpressionConstructor::newCode(
				OperatorManager::OPERATOR_RSHIFT,
				bfValue, additiveExpression()) );
	}
//	)?
	return bfValue;
}

Operator * ExpressionParser::shiftOp()
{
	if (next_token_is(Token::T_LSHIFT))
	{
		return OperatorManager::OPERATOR_LSHIFT;
	}
	else if (next_token_is(Token::T_RSHIFT))
	{
		return OperatorManager::OPERATOR_RSHIFT;
	}

	return OperatorManager::OPERATOR_NULL;
}


BF ExpressionParser::additiveExpression()
{
	BF bfValue = multiplicativeExpression();
//	( additiveOp();
	while (true)
	{
		if (next_token_is(Token::T_ADD))
		{
			bfValue = ExpressionConstructor::addExpr(
					bfValue, multiplicativeExpression());
		}
		else if(next_token_is(Token::T_SUB))
		{
			bfValue = ExpressionConstructor::minusExpr(
					bfValue, multiplicativeExpression());
		}
		else
		{
			break;
		}
	}
//	)*
	return bfValue;
}

Operator * ExpressionParser::additiveOp()
{
	if (next_token_is(Token::T_ADD))
	{
		return OperatorManager::OPERATOR_PLUS;
	}
	else if (next_token_is(Token::T_SUB))
	{
		return OperatorManager::OPERATOR_MINUS;
	}

	return OperatorManager::OPERATOR_NULL;
}


BF ExpressionParser::multiplicativeExpression()
{
	BF bfValue = powerExpression();
//	( multiplicativeOp();
	while (true)
	{
		if (next_token_is(Token::T_MULT))
		{
			bfValue = ExpressionConstructor::multExpr(bfValue, powerExpression());
		}
		if (next_token_is(Token::T_DIV))
		{
			bfValue = ExpressionConstructor::divExpr(bfValue, powerExpression());
		}
		else
		{
			break;
		}
	}
//	)*
	return bfValue;
}

Operator * ExpressionParser::multiplicativeOp()
{
	if (next_token_is(Token::T_MULT))
	{
		return OperatorManager::OPERATOR_MULT;
	}
	else if (next_token_is(Token::T_DIV))
	{
		return OperatorManager::OPERATOR_DIV;
	}

	return OperatorManager::OPERATOR_NULL;
}


BF ExpressionParser::powerExpression()
{
	BF bfValue = unaryExpression();
//	( POW : Right Associativity => Binary to start
	if (next_token_is(Token::T_POW))
	{
		return ExpressionConstructor::powExpr(bfValue, unaryExpression());
	}
	else if (next_token_is(Token::T_MOD))
	{
		return ExpressionConstructor::modExpr(bfValue, powerExpression());
	}
//	)?
	return bfValue;
}



BF ExpressionParser::unaryExpression()
{
	if (next_token_is(Token::T_ADD))
	{
		return primaryExpression();
	}
	else if (next_token_is(Token::T_SUB))
	{
		return ExpressionConstructor::uminusExpr( primaryExpression() );
	}

//	else if (next_token_is(Token::T_INCR))
//	{
//		primaryExpression();
//	}
//	else if (next_token_is(Token::T_DECR))
//	{
//		primaryExpression();
//	}

	else if (next_token_is(Token::T_LNOT) || next_token_symbol_is("not"))
	{
		return ExpressionConstructor::notExpr( primaryExpression() );
	}
	else if (next_token_is(Token::T_BNOT))
	{
		return ExpressionConstructor::bnotExpr( primaryExpression() );
	}

	else if (token_symbol_is("newfresh"))
	{
		return ExpressionConstructor::newExpr(
				OperatorManager::OPERATOR_ASSIGN_NEWFRESH,
				primaryExpression());
	}

//	| primaryExpression(); ( INCR | DECR )?

	else
	{
		return primaryExpression();
	}
}



BF ExpressionParser::primaryExpression()
{
	if (next_token_is(Token::T_LPAREN))
	{
		BF bfValue = parseExpression();

		if (! next_token_is(Token::T_RPAREN))
		{
			throw DiversityError( "Expected token< ')' > for ( expression ) recognition !" );
		}

		return bfValue;
	}

//	| expression_invoke();

	else
	{
		return literalExpression();
	}
}


BF ExpressionParser::literalExpression()
{
	if (token_is(Token::T_NUMBER))
	{
		BF bfValue = ExpressionConstructor::newExprNumber(
				current_token().value);

		advance_token();

		return bfValue;
	}

	else if (next_token_symbol_is("true"))
	{
		return ExpressionConstant::BOOLEAN_TRUE;
	}
	else if (next_token_symbol_is("false"))
	{
		return ExpressionConstant::BOOLEAN_FALSE;
	}

	else if (token_is(Token::T_SYMBOL))
	{
		const BF & bfValue = machineCtx.getsemObjectByNameID(
				current_token().value);
		if( bfValue.invalid() )
		{
			throw DiversityError( "Unfound symbol for literal expression" );
		}

		advance_token();

		return( bfValue );
	}

	else if (token_is(Token::T_STRING_DQ))
	{
		BF bfValue = ExpressionConstructor::newDoubleQuoteString(
				current_token().value);

		advance_token();

		return bfValue;
	}

	else if (token_is(Token::T_STRING_SQ))
	{
		BF bfValue = ExpressionConstructor::newSingleQuoteString(
				current_token().value);

		advance_token();

		return bfValue;
	}

//	| CharacterLiteral
//	| SymbolOperator
//	| anArray
//	| aList

	else
	{
		throw DiversityError( "Unexpected token for literal expression" );

		return BF::REF_NULL;
	}
}


/**
 * COMPILER
 */
bool ExpressionParser::compile()
{
	if( lexer.process() )
	{
		if( ! lexer.empty() )
		{
AVM_IF_DEBUG_FLAG( PARSING )

	lexer.printTokens();

AVM_ENDIF_DEBUG_FLAG( PARSING )

			// Initialization
			lexer.begin();

			next_token();

			// Parsing
			bfExpression = parseExpression();

			if (token_is(Token::T_SEMI))
			{
				if (! lexer.finished())
				{
					throw DiversityError( "Found token< 'EOF' > but there are anything else to parse !" );
				}
			}
			else
			{
				throw DiversityError( "Expected token< ';' > for end of expression recognition !" );
			}

			std::cout << std::endl;

			if( hasError() )
			{
				std::cout << "Error:> " << error() <<std::endl;
			}

			return true;
		}
		else
		{
			OUT_ERR << "Lexer without token !";

			return false;
		}
	}
	else
	{
		OUT_ERR << "Lexer error !";

		return false;
	}
}


BF ExpressionParser::parse(
		const Machine & machineCtx, const std::string & rawExpression)
{
	ExpressionParser exprParser( machineCtx, rawExpression);

	if( exprParser.compile() )
	{
		return exprParser.result();
	}

	const BF & objExpr = machineCtx.getsemObjectByNameID(rawExpression);
	if( objExpr.valid() )
	{
		return( objExpr );
	}

	return( ExpressionConstant::INTEGER_42 );
}

const BF & ExpressionParser::parseVariable(
		const Machine & machineCtx, const std::string & varID)
{
	return( machineCtx.getsemVariable(varID) );
}


}
