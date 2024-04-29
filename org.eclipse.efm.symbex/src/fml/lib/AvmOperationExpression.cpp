/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmOperationExpression.h"

#include <fml/executable/BaseInstanceForm.h>

#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{


std::map< std::string , const Operator * > AvmOperationExpression::theOtherMap;




/**
 * LOADER
 */
void AvmOperationExpression::load()
{
	putOther("random"  , OperatorManager::OPERATOR_RANDOM);

	putOther("abs"     , OperatorManager::OPERATOR_ABS);

	putOther("ceil"    , OperatorManager::OPERATOR_CEIL);
	putOther("floor"   , OperatorManager::OPERATOR_FLOOR);
	putOther("round"   , OperatorManager::OPERATOR_ROUND);
	putOther("trunc"   , OperatorManager::OPERATOR_TRUNCATE);

	// EXP - LOG
	putOther("sqrt"    , OperatorManager::OPERATOR_SQRT);

	putOther("exp"     , OperatorManager::OPERATOR_EXP);
	putOther("ln"      , OperatorManager::OPERATOR_LN);
	putOther("log"     , OperatorManager::OPERATOR_LOG);

	// TRIGONOMETRIC
	putOther("sin"     , OperatorManager::OPERATOR_SIN);
	putOther("cos"     , OperatorManager::OPERATOR_COS);
	putOther("tan"     , OperatorManager::OPERATOR_TAN);

	putOther("sinh"    , OperatorManager::OPERATOR_SINH);
	putOther("cosh"    , OperatorManager::OPERATOR_COSH);
	putOther("tanh"    , OperatorManager::OPERATOR_TANH);

	putOther("asin"    , OperatorManager::OPERATOR_ASIN);
	putOther("acos"    , OperatorManager::OPERATOR_ACOS);
	putOther("atan"    , OperatorManager::OPERATOR_ATAN);
	putOther("atan2"   , OperatorManager::OPERATOR_ATAN2);

	putOther("asinh"   , OperatorManager::OPERATOR_ASINH);
	putOther("acosh"   , OperatorManager::OPERATOR_ACOSH);
	putOther("atanh"   , OperatorManager::OPERATOR_ATANH);
}


/**
 * DISPOSER
 */
void AvmOperationExpression::dispose()
{
	theOtherMap.clear();
}


} /* namespace sep */
