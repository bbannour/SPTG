/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 juin 2016
 *
 * Contributors:
 *  Stephane Salmons (CEA LIST) stephane.salmons@gmail.com
 *   - Initial API and Implementation
 ******************************************************************************/

#include "boost/test/unit_test.hpp"


#include <fml/expression/ExpressionConstructor.h>


using namespace std;
using namespace sep;

BOOST_AUTO_TEST_SUITE (FML);

BOOST_AUTO_TEST_CASE (t_exprctor_newinteger) {
	BOOST_CHECK_MESSAGE ("512" == ExpressionConstructor::newExprInteger("512").str(), "newExprInteger(512) != 512");
}


BOOST_AUTO_TEST_CASE (t_exprctor_newinteger_decimal_excp) {
	BOOST_CHECK_MESSAGE ("5" == ExpressionConstructor::newExprInteger("5.12").str(), "newExprInteger(5.12) != 5");
}

BOOST_AUTO_TEST_CASE (t_exprctor_newinteger_NULL) {
	BOOST_CHECK_MESSAGE ("0" == ExpressionConstructor::newExprInteger(NULL).str(), "newExprInteger(NULL) != 0");
}


BOOST_AUTO_TEST_CASE (t_exprctor_newrational_dec2frac) {
	BOOST_CHECK_MESSAGE ("128/25" == ExpressionConstructor::newExprRational("5.12").str(), "newExprRational(5.12) != 128/25");
}

BOOST_AUTO_TEST_CASE (t_exprctor_newrational_dec2dec) {
	BOOST_CHECK_MESSAGE ("5.12" == ExpressionConstructor::newExprRational("5.12").str(), "newExprRational(5.12) !=5.12");
}


BOOST_AUTO_TEST_SUITE_END(); // FML
