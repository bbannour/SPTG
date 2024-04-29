/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 9 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONFACTORY_H_
#define EXPRESSIONFACTORY_H_

#include <common/BF.h>

#include <collection/BFContainer.h>
#include <collection/Typedef.h>

#include <fml/executable/BaseInstanceForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>


namespace sep
{


class ExpressionFactory
{
public:

	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * CONFIGURE
	 */
	static bool configure();


	/**
	* NUMERIC or SIMPLE TYPE TEST & CAST
	*/
	static bool isBoolean(const BF & value);
	static bool toBoolean(const BF & value);

	/**
	 * COMPARISON
	 * with TRUE & FALSE
	 */
	static bool isEqualFalse(const BF & value);
	static bool isNotEqualFalse(const BF & value);

	static bool isEqualTrue(const BF & value);
	static bool isNotEqualTrue(const BF & value);


	static bool isNumber(const BF & value);

	inline static bool isNumeric(const BF & value)
	{
		return( isNumber(value) );
	}

	static bool isInt32(const BF & value);
	static std::int32_t toInt32(const BF & value);

	static bool isInt64(const BF & value);
	static std::int64_t toInt64(const BF & value);

	static bool isInteger(const BF & value);
	static avm_integer_t toInteger(const BF & value);

	static bool isPosInteger(const BF & value);

	static bool isUInteger(const BF & value);
	static avm_uinteger_t toUInteger(const BF & value);

	static bool isRational(const BF & value);
	static avm_integer_t toDenominator(const BF & value);
	static avm_integer_t toNumerator(const BF & value);

	static bool isFloat(const BF & value);
	static avm_float_t toFloat(const BF & value);

	static bool isReal(const BF & value);
	static avm_real_t toReal(const BF & value);


	static bool isCharacter(const BF & value);
	static char toCharacter(const BF & value);

	static bool isIdentifier(const BF & value);
	static std::string toIdentifier(const BF & value);

	static bool isUfi(const BF & value);
	static std::string toUfi(const BF & value);

	static bool isUfid(const BF & value);
	static std::string toUfid(const BF & value);

	static bool isEnumSymbol(const BF & value);
	static std::string strEnumSymbol(const BF & value);

	static bool isBuiltinString(const BF & value);
	static std::string toBuiltinString(const BF & value);


	static bool isBuiltinValue(const BF & value);

	static bool isConstValue(const BF & value);


	/**
	 * COLLECT VARIABLE OR CLAUSE
	 */
	static void collectVariable(const BF & anExpr, BFCollection & listOfVar);

	static void collectVariable(const BFCode & aCode, BFCollection & listOfVar);


	inline static void collectVariable(const BF & anExpr,
			VectorOfBaseInstanceForm & listOfElement)
	{
		BFVector listOfVar;

		collectVariable(anExpr, listOfVar);

		BFVector::raw_iterator< InstanceOfData > itVar = listOfVar.begin();
		BFVector::raw_iterator< InstanceOfData > endVar = listOfVar.end();
		for( ; itVar != endVar ; ++itVar )
		{
			listOfElement.append( itVar );
		}
	}


	static void collectsFreeVariable(const BF & anExpr,
			BFCollection & listOfBoundVar, BFCollection & listOfVar);

	static void collectsFreeVariable(const BFCode & aCode,
			BFCollection & listOfBoundVar, BFCollection & listOfVar);


	static bool containsVariable(const BF & anExpr, InstanceOfData * aVariable);

	static bool containsVariable(const BFCode & aCode, InstanceOfData * aVariable);


	static bool containsVariable(const BF & anExpr, BFCollection & listOfVar);

	static bool containsVariable(const BFCode & aCode, BFCollection & listOfVar);


	static void collectsClause(const BF & anExpr, BFCollection & listOfClause);

	static void collectsClause(const BFCode & aCode, BFCollection & listOfClause);


	static void collectsClause(const BF & anExpr, BFCollection & listOfBoundVar,
			BFCollection & listOfBoundClause, BFCollection & listOfFreeClause);

	static void collectsClause(const BFCode & aCode, BFCollection & listOfBoundVar,
			BFCollection & listOfBoundClause, BFCollection & listOfFreeClause);


	static void deduceTrivialAssignmentsFromConjonction(
			const BF & anExpr, BFCodeCollection & listOfAssignments);

};


}

#endif /* EXPRESSIONFACTORY_H_ */
