/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 sept. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef STATEMENTCONSTRUCTOR_H_
#define STATEMENTCONSTRUCTOR_H_

#include <fml/expression/AvmCodeFactory.h>


namespace sep
{

class StatementConstructor  :  public AvmCodeFactory
{

public:
	/**
	 * NOP STATEMENT
	 */
	inline static BFCode nopCode()
	{
		return( StatementConstructor::newCode( OperatorManager::OPERATOR_NOP ) );
	}


	/**
	 * ASSIGMENT OP STATEMENT
	 *  :=  +=  -=  *=  /= "  %=  ^='
	 */
	inline static BFCode assignOpExpr(
			const Operator * anOperator, const BF & arg1, const BF & arg2)
	{
		return( newCode(OperatorManager::OPERATOR_ASSIGN_OP, arg1,
				newCode(anOperator, arg2)) );
	}



};


}

#endif /* STATEMENTCONSTRUCTOR_H_ */
