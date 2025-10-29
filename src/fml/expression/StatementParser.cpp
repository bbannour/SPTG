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

#include "StatementParser.h"

#include <common/GeneralException.h>
#include <fml/expression/StatementConstructor.h>

#include <fml/infrastructure/Machine.h>

#include <fml/operator/OperatorManager.h>


namespace sep
{


/**
 * PARSER STATEMENT RULES
 */
BFCode StatementParser::parseStatements()
{
	BFCode statement( OperatorManager::OPERATOR_SEQUENCE );

	while (! lexer.finished())
	{
		statement.append( parseStatement() );

		if (next_token_is(Token::T_SEMI))
		{
			continue;
		}
		else
		{
			DiversityError("Expected token< ';' > for statements recognition !" );
		}
	}

	return statement;
}


BFCode StatementParser::parseStatement()
{
	if( next_token_symbol_is("input") )
	{
		return( parseInputStatement() );
	}
	else if( next_token_symbol_is("output") )
	{
		return( parseOutputStatement() );
	}

	else if( next_token_symbol_is("guard") )
	{
		return( parseGuardStatement() );
	}

	else if( next_token_symbol_is("tguard") )
	{
		return( parseTGuardStatement() );
	}

	else if( next_token_symbol_is("newfresh") )
	{
		return( parseNewFreshStatement() );
	}

	else if( token_is(Token::T_SYMBOL) )
	{
		return( parseAssigntatement() );
	}

	else
	{
		throw DiversityError("Expected token< input | output | guard | tguard "
				"| newfreh | assignment > for statement recognition !");
	}

	return( StatementConstructor::nopCode() );
}


BFCode StatementParser::parseInputStatement()
{
	BFCode statement( OperatorManager::OPERATOR_INPUT );


	if (token_is(Token::T_SYMBOL))
	{
		const BF & bfValue = machineCtx.getsemPort(current_token().value);
		if( bfValue.valid() )
		{
			statement.append( bfValue );
		}
		else
		{
			throw DiversityError( "Unfound port symbol for "
					"input port( expression ,+ ) recognition !" );
		}

		advance_token();
	}
	else
	{
		throw DiversityError( "Expected token::SYMBOL as port for "
				"input port( expression ,+ ) recognition !" );
	}

	if (next_token_is(Token::T_LPAREN))
	{
		while (! next_token_is(Token::T_RPAREN))
		{
			statement.append( parseExpression() );

			if (next_token_is(Token::T_COMMA))
			{
				continue;
			}
			else if (next_token_is(Token::T_RPAREN))
			{
				break;
			}
			else
			{
				throw DiversityError("Expected token< ')' > "
						"for input port( expression ,+ ) recognition !" );
			}
		}
	}

	return statement;
}


BFCode StatementParser::parseOutputStatement()
{
	BFCode statement( OperatorManager::OPERATOR_OUTPUT );

	if (token_is(Token::T_SYMBOL))
	{
		const BF & bfValue = machineCtx.getsemPort(current_token().value);
		if( bfValue.valid() )
		{
			statement.append( bfValue );
		}
		else
		{
			throw DiversityError( "Unfound port symbol for "
					"output port( expression ,+ ) recognition !");
		}

		advance_token();
	}
	else
	{
		throw DiversityError( "Expected token::SYMBOL as port for "
				"output port( expression ,+ ) recognition !" );
	}

	if (next_token_is(Token::T_LPAREN))
	{
		while (! next_token_is(Token::T_RPAREN))
		{
			statement.append( parseExpression() );

			if (next_token_is(Token::T_COMMA))
			{
				continue;
			}
			else if (next_token_is(Token::T_RPAREN))
			{
				break;
			}
			else
			{
				throw DiversityError( "Expected token< ')' > for "
						"output port( expression ,+ ) recognition !" );
			}
		}
	}

	return statement;
}


BFCode StatementParser::parseGuardStatement()
{
	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_GUARD, parseExpression()) );
}


BFCode StatementParser::parseTGuardStatement()
{
	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_TIMED_GUARD, parseExpression()) );
}


BFCode StatementParser::parseNewFreshStatement()
{
	return( StatementConstructor::newCode(
			OperatorManager::OPERATOR_ASSIGN_NEWFRESH, parseExpression()) );
}


BFCode StatementParser::parseAssigntatement()
{
	const BF & bfVar = machineCtx.getsemVariable(current_token().value);
	if( bfVar.invalid() )
	{
		DiversityError( "Unfound variable symbol for assignment recognition !" );
	}

	advance_token();

	if (next_token_is(Token::T_ASSIGN))
	{
		return StatementConstructor::newCode(
				OperatorManager::OPERATOR_ASSIGN, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_ADD_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_PLUS, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_SUB_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MINUS, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_MULT_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MULT, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_DIV_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_DIV, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_POW_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_POW, bfVar, parseExpression());
	}
	else if (next_token_is(Token::T_MOD_ASSIGN))
	{
		return StatementConstructor::assignOpExpr(
				OperatorManager::OPERATOR_MOD, bfVar, parseExpression());
	}
	else
	{
		throw DiversityError("Expected token< '=' | ':=' | '+=' | '-=' | '*=' | '/=' "
				"| '%=' | '^=' > for assignment recognition !" );
	}

	return BFCode::REF_NULL;
}



/**
 * COMPILER
 */
bool StatementParser::compile()
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
			bfStatement = parseStatement();

			if (token_is(Token::T_SEMI))
			{
				if (! lexer.finished())
				{
					DiversityError( "Found token< 'EOF' > but there are anything else to parse !" );
				}
			}
			else
			{
				DiversityError( "Expected token< ';' > for end of statement recognition !" );
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


BFCode StatementParser::parse(
		const Machine & machineCtx, const std::string & rawStatement)
{
	StatementParser stmtParser( machineCtx, rawStatement);

	if( stmtParser.compile() )
	{
		return stmtParser.result();
	}

	return( StatementConstructor::nopCode() );
}

}
