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

#ifndef PARSER_ANTLR4ERRORFACTORY_H_
#define PARSER_ANTLR4ERRORFACTORY_H_

#include <cstddef>
#include <string>
#include <BaseErrorListener.h>
#include <DefaultErrorStrategy.h>


namespace sep
{

/**
 * ANTLR ERROR STRATEGY
 */

class SymbexErrorStrategy final : public antlr4::DefaultErrorStrategy
{
protected:
	virtual void reportNoViableAlternative(antlr4::Parser * recognizer,
			const antlr4::NoViableAltException & e) override;

};

/**
 * ANTLR ERROR LISTENER
 */

class SymbexErrorListener : public antlr4::BaseErrorListener
{

	virtual void syntaxError(antlr4::Recognizer * recognizer,
			antlr4::Token * offendingSymbol, std::size_t line,
			std::size_t charPositionInLine, const std::string & msg,
			std::exception_ptr e) override;

	void underlineError(antlr4::Recognizer * recognizer,
			antlr4::Token * offendingToken,
			std::size_t line, std::size_t charPositionInLine);

};


} /* namespace sep */

#endif /* PARSER_ANTLR4ERRORFACTORY_H_ */
