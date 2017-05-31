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

#ifndef AVM_MODEL_EXPRESSION_EXPRESSIONCONSTANT_H_
#define AVM_MODEL_EXPRESSION_EXPRESSIONCONSTANT_H_

#include <common/BF.h>

#include <fml/numeric/Numeric.h>


namespace sep
{


class ExpressionConstant
{

public:
	/**
	 * CONSTANT EXPRESSION
	 */
	static BF BOOLEAN_TRUE;
	static BF BOOLEAN_FALSE;

	static BF CHARACTER_NULL;

	static BF STRING_EMPTY;

	static Numeric INTEGER_MINUS_TWO;
	static Numeric INTEGER_MINUS_ONE;
	static Numeric INTEGER_ZERO;
	static Numeric INTEGER_ONE;
	static Numeric INTEGER_TWO;


	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////
	static void load();
	static void dispose();

};

} /* namespace sep */

#endif /* AVM_MODEL_EXPRESSION_EXPRESSIONCONSTANT_H_ */
