/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 sept. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExpressionConstant.h"

#include <fml/builtin/Boolean.h>
#include <fml/builtin/Character.h>
#include <fml/numeric/Integer.h>
#include <fml/builtin/String.h>

namespace sep
{


/**
 * CONSTANT EXPRESSION
 */
BF ExpressionConstant::BOOLEAN_TRUE;

BF ExpressionConstant::BOOLEAN_FALSE;


BF ExpressionConstant::CHARACTER_NULL;

BF ExpressionConstant::STRING_EMPTY;


Numeric ExpressionConstant::INTEGER_MINUS_TWO;

Numeric ExpressionConstant::INTEGER_MINUS_ONE;

Numeric ExpressionConstant::INTEGER_ZERO;

Numeric ExpressionConstant::INTEGER_ONE;

Numeric ExpressionConstant::INTEGER_TWO;


////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

void ExpressionConstant::load()
{
	BOOLEAN_TRUE      = Boolean::create(true);

	BOOLEAN_FALSE     = Boolean::create(false);


	INTEGER_MINUS_TWO = -2;

	INTEGER_MINUS_ONE = -1;

	INTEGER_ZERO      = 0;

	INTEGER_ONE       = 1;

	INTEGER_TWO       = 2;


	CHARACTER_NULL    = new Character('\0');

	STRING_EMPTY      = String::create("");
}


void ExpressionConstant::dispose()
{
	BOOLEAN_TRUE.destroy();
	BOOLEAN_FALSE.destroy();

	INTEGER_MINUS_TWO.destroy();
	INTEGER_MINUS_ONE.destroy();

	INTEGER_ZERO.destroy();

	INTEGER_ONE.destroy();
	INTEGER_TWO.destroy();

	CHARACTER_NULL.destroy();
	STRING_EMPTY.destroy();
}


} /* namespace sep */
