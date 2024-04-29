/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 janv. 2018
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Antlr4ErrorFactory.h"

#include <util/avm_string.h>

#include <antlr4-runtime/CharStream.h>
#include <antlr4-runtime/CommonToken.h>
#include <antlr4-runtime/CommonTokenStream.h>
#include <antlr4-runtime/NoViableAltException.h>
#include <antlr4-runtime/Parser.h>

namespace sep
{


/**
 * ANTLR ERROR STRATEGY
 */
void SymbexErrorStrategy::reportNoViableAlternative(
		antlr4::Parser * recognizer, const antlr4::NoViableAltException & e)
{
	antlr4::TokenStream * tokenStream = recognizer->getTokenStream();
	std::string input;
	if( tokenStream != nullptr )
	{
		if( e.getStartToken()->getType() == antlr4::Token::EOF )
		{
			input = "<EOF>";
		} else
		{
//				input = tokens->getText(e.getStartToken(), e.getOffendingToken());

			std::string inputString =
				tokenStream->getTokenSource()->getInputStream()->toString();

			input = StringTools::string_split(inputString,
					'\n', e.getOffendingToken()->getLine());
		}
	}
	else
	{
		input = "<unknown input>";
	}
	std::string msg = "no viable alternative at input "
			+ escapeWSAndQuote(input);
	recognizer->notifyErrorListeners(
			e.getOffendingToken(), msg, std::make_exception_ptr(e));
}

/**
 * ANTLR ERROR LISTENER
 */
void SymbexErrorListener::syntaxError(antlr4::Recognizer * recognizer,
			antlr4::Token * offendingSymbol, std::size_t line,
			std::size_t charPositionInLine, const std::string & msg,
			std::exception_ptr e)
{
//	static std::size_t ERROR_COUNT = 0;
//	std::cerr << "Syntax Error: " << (++ERROR_COUNT) << std::endl;

	std::vector<std::string> stack =
			((antlr4::Parser *)recognizer)->getRuleInvocationStack();
//		Collections.reverse(stack);
	std::cerr << "Rule Stack: ";
	for( const auto & rule : stack )
	{
		std::cerr << " <-- " << rule;
	}
	std::cerr << std::endl;

	std::cerr << "Token: " << offendingSymbol->getText() << std::endl;

	std::cerr << "line " << line << ":" << charPositionInLine << " at "
			<< ((antlr4::CommonToken *)offendingSymbol)->toString(recognizer)
			<< ":\n\t" << msg << std::endl;


	underlineError(recognizer,offendingSymbol, line, charPositionInLine);
}


void SymbexErrorListener::underlineError(antlr4::Recognizer * recognizer,
		antlr4::Token * offendingToken,
		std::size_t line, std::size_t charPositionInLine)
{
	antlr4::CommonTokenStream * tokenStream =
			(antlr4::CommonTokenStream *)recognizer->getInputStream();
	std::string inputString =
			tokenStream->getTokenSource()->getInputStream()->toString();
//	std::cerr << inputString << std::endl;

	std::string errorLine = StringTools::string_split(inputString, '\n', line);
	std::cerr << errorLine << std::endl;
	for( std::size_t i = 0 ; i < charPositionInLine ; ++i )
	{
		std::cerr << ( (errorLine[i] == '\t') ? '\t' : ' ' );
	}

	std::size_t start = offendingToken->getStartIndex();
	std::size_t stop = offendingToken->getStopIndex();
	if( (start >= 0) && (stop >= 0) )
	{
		for( std::size_t i = start ; i <= stop ; ++i )
		{
			std::cerr << "^";
		}
	}
	std::cerr << std::endl;
}


} /* namespace sep */

