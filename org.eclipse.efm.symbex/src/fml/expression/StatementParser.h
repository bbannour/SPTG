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

#ifndef STATEMENTPARSER_H_
#define STATEMENTPARSER_H_

#include "ExpressionParser.h"

#include <fml/expression/AvmCode.h>


namespace sep
{

class Machine;


class StatementParser  :  public ExpressionParser
{

protected:
	/**
	 * ATTRIBUTES
	 */
	BFCode bfStatement;


	/**
	 * CONTRUCTORS
	 */
	StatementParser(const Machine & machine, const std::string & rawStatement)
	: ExpressionParser( machine , rawStatement ),
	bfStatement( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~StatementParser()
	{
		//!! NOTHING
	}


	/**
	 * GETTERS
	 */
	inline const BFCode & result() const
	{
		return bfStatement;
	}

	/**
	 * COMPILER
	 */
	bool compile();


public:
	/**
	 * PARSER STATEMENT RULES
	 */
	BFCode parseStatements();

	BFCode parseStatement();

	BFCode parseInputStatement();

	BFCode parseOutputStatement();

	BFCode parseGuardStatement();

	BFCode parseTGuardStatement();

	BFCode parseNewFreshStatement();

	BFCode parseAssigntatement();

	static BFCode parse(
			const Machine & machineCtx, const std::string & rawStatement);

};

}

#endif /* STATEMENTPARSER_H_ */
