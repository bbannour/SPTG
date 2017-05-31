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


#include <fml/numeric/Numeric.h>


using namespace std;
using namespace sep;


BOOST_AUTO_TEST_SUITE (FML);

BOOST_AUTO_TEST_CASE (t_numeric_ctor) {
	Numeric N("512");
	BOOST_CHECK ("512" == N.str());
}

BOOST_AUTO_TEST_CASE (t_numeric_ctor_decimal_excp) {
	Numeric N("5.12");
}

BOOST_AUTO_TEST_CASE (t_numeric_ctor_decimal) {
	Numeric N("5.12");
	BOOST_CHECK ("5.12" == N.str());

}

BOOST_AUTO_TEST_CASE (t_numeric_ctor_frac) {
	Numeric N("5/12");
	BOOST_CHECK ("5/12" == N.str());
}

BOOST_AUTO_TEST_CASE (t_numeric_frac_simplif) {
	Numeric N("512/100");
	BOOST_CHECK ("128/25" == N.str());
}

BOOST_AUTO_TEST_SUITE_END(); // FML
