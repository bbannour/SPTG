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

#include <iostream>

#include "boost/test/unit_test.hpp"

#include "fml/numeric/Float.h"
#include "util/avm_numeric.h"

using namespace std;
using namespace sep;


BOOST_AUTO_TEST_SUITE (FML);

BOOST_AUTO_TEST_CASE (t_float_ctor) {
	Float F("123456789123456789123456789123456789");
}

BOOST_AUTO_TEST_CASE (t_float_big) {
	Float F("123456789123456789123456789123456789");
	BOOST_CHECK_MESSAGE("123456789123456789123456789123456789" == F.str(), F.str() << " is not " << "123456789123456789123456789123456789");
	BOOST_CHECK (! F.isInt32());
	BOOST_CHECK (! F.isInt64());
	BOOST_CHECK (! F.isInteger());
	BOOST_CHECK (! F.isPosInteger());
}

BOOST_AUTO_TEST_CASE (t_float_maxuint) {
	Float F(AVM_NUMERIC_MAX_UINT);
	BOOST_CHECK (  F.isInt32());
	BOOST_CHECK (  F.isInt64());
	BOOST_CHECK (  F.isInteger());
	BOOST_CHECK (! F.isPosInteger());
}

BOOST_AUTO_TEST_CASE (t_float_maxlong) {
	Float F(AVM_NUMERIC_MAX_LONG);
	BOOST_CHECK ( F.isInt32());
	BOOST_CHECK ( F.isInt64());
	BOOST_CHECK ( F.isInteger());
	BOOST_CHECK ( F.isPosInteger());
}

BOOST_AUTO_TEST_SUITE_END(); // FML
