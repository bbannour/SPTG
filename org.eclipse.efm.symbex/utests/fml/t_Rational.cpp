/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 juin 2016
 *
 * Contributors:
 *  Stephane Salmons (CEA LIST) stephane.salmons@gmail.com
 *   - Initial API and Implementation
 ******************************************************************************/

#include <iostream>

#include "boost/test/unit_test.hpp"

#include "fml/numeric/Rational.h"
#include "util/avm_numeric.h"

using namespace std;
using namespace sep;


BOOST_AUTO_TEST_SUITE (FML);

BOOST_AUTO_TEST_CASE (t_rational_ctor) {
	Rational R("123456789123456789123456789123456789/3");
	Rational S("123456789123456789123456789.123456788");
}

BOOST_AUTO_TEST_CASE (t_rational_big) {
	Rational R("123456789123456789123456789123456789/3");
	BOOST_CHECK_MESSAGE ("41152263041152263041152263041152263" == R.str(), "str conversion failed");
	BOOST_CHECK_MESSAGE (! R.isInt32(), "is Int32");
	BOOST_CHECK_MESSAGE (! R.isInt64(), "is Int64");
	BOOST_CHECK_MESSAGE (! R.isInteger(), "is Integer");
	BOOST_CHECK_MESSAGE (! R.isPosInteger(), "is PosInteger");
}

BOOST_AUTO_TEST_CASE (t_rational_maxuint) {
	Rational R(AVM_NUMERIC_MAX_UINT);
	BOOST_CHECK_MESSAGE (! R.isInt32(),"is Int32");
	BOOST_CHECK_MESSAGE (  R.isInt64(), "is not Int64");
	BOOST_CHECK_MESSAGE (  R.isInteger(), "is not Integer");
	BOOST_CHECK_MESSAGE (  R.isPosInteger(), "is not PosInteger");
}

BOOST_AUTO_TEST_CASE (t_rational_maxlong) {
	Rational R(AVM_NUMERIC_MAX_LONG);
	BOOST_CHECK_MESSAGE ( R.isInt32(),"is not Int32");
	BOOST_CHECK_MESSAGE ( R.isInt64(), "is not Int64");
	BOOST_CHECK_MESSAGE ( R.isInteger(), "is not Integer");
	BOOST_CHECK_MESSAGE ( R.isPosInteger(), "is not PosInteger");
}

BOOST_AUTO_TEST_CASE (t_rational_decimal_big) {
	Rational S("123456789123456789123456789.123456788");
	BOOST_CHECK_MESSAGE ("30864197280864197280864197280864197/250000000" == S.str(), "Rational(123456789123456789123456789.123456788) != 30864197280864197280864197280864197/250000000");
	BOOST_CHECK_MESSAGE (! S.isInt32(), "is Int32");
	BOOST_CHECK_MESSAGE (! S.isInt64(), "is Int64");
	BOOST_CHECK_MESSAGE (! S.isInteger(), "is Integer");
	BOOST_CHECK_MESSAGE (! S.isPosInteger(),  "is PosInteger");
}

BOOST_AUTO_TEST_SUITE_END(); // FML
