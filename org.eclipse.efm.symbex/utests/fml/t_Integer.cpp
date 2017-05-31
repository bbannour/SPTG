/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 juin 2016
 *
 * Contributors:
 *  Stephane Salmons (CEA LIST) stephane.salmons@gmail.com
 *   - Initial API and Implementation
 ******************************************************************************/

#include <iostream>

#include "boost/test/unit_test.hpp"


#include "fml/numeric/Integer.h"
#include "util/avm_numeric.h"

using namespace std;
using namespace sep;




BOOST_AUTO_TEST_SUITE (FML);

BOOST_AUTO_TEST_CASE (t_integer_ctor) {Integer N("123456789123456789123456789123456789") ;}

BOOST_AUTO_TEST_CASE (t_integer_big) {
	Integer N("123456789123456789123456789123456789");
	BOOST_CHECK_MESSAGE ("123456789123456789123456789123456789" == N.str(), "string conversion error");
	BOOST_CHECK_MESSAGE (! N.isInt32(), "is Int32");
	BOOST_CHECK_MESSAGE (! N.isInt64(), "is Int64");
	BOOST_CHECK_MESSAGE (! N.isInteger(), "is Integer" );
	BOOST_CHECK_MESSAGE (! N.isPosInteger(), "is PosInteger");
}

BOOST_AUTO_TEST_CASE (t_integer_maxuint) {
	Integer N(AVM_NUMERIC_MAX_UINT);
	BOOST_CHECK_MESSAGE (! N.isInt32(), "is Int32");
	BOOST_CHECK_MESSAGE (! N.isInt64(), "is Int64");
	BOOST_CHECK_MESSAGE (! N.isInteger(), "is Integer");
	BOOST_CHECK_MESSAGE (  N.isPosInteger(), "is not PosInteger");
}

BOOST_AUTO_TEST_CASE (t_integer_maxlong) {
	Integer N(AVM_NUMERIC_MAX_LONG);
	BOOST_CHECK_MESSAGE ( N.isInt32(), "is not Int32");
	BOOST_CHECK_MESSAGE ( N.isInt64(), "is not Int64");
	BOOST_CHECK_MESSAGE ( N.isInteger(),  "is not Integer");
	BOOST_CHECK_MESSAGE ( N.isPosInteger(), "is not PosInteger");
}

BOOST_AUTO_TEST_CASE (t_integer_10pow123) {
	string computed(Integer::pow(10, 123).str());
	string expected("1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
	BOOST_CHECK_MESSAGE (computed == expected, "pow(10,123) not equals its decimal representation");
}


BOOST_AUTO_TEST_SUITE_END(); // FML
