/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 06 july 2016
 *
 * Contributors:
 *  Stephane Salmons (CEA LIST) stephane.salmons@gmail.com
 *   - Initial API and Implementation
 ******************************************************************************/
/*
* GiNaC is a C++ library. 
* GiNaC is an iterated and recursive acronym for GiNaC is Not a CAS,
* where CAS stands for Computer Algebra System.
* It is designed to allow the creation of integrated systems that
* embed symbolic manipulations together with more established areas of
* computer science
* http://www.ginac.de/
*
*/




/*

test on optional library that is not yet integrated into diversity install process


* /




/*
#include "boost/test/unit_test.hpp"


#include <fml/symbol/Symbol.h>

#include <ginac/ginac.h>
#include <compat/model/ginac_expression/ExpressionGinac.h>
#include <compat/model/ginac_expression/GinacAnd.h>
#include <compat/model/ginac_expression/GinacForm.h>
#include <compat/model/ginac_expression/GinacNot.h>
#include <compat/model/ginac_expression/GinacOr.h>
#include <compat/model/ginac_expression/GinacRelational.h>
#include <compat/model/ginac_expression/GinacSimplifier.h>




//using namespace std;
using namespace sep;

BOOST_AUTO_TEST_SUITE(FML);

BOOST_AUTO_TEST_CASE(t_ginac_expression_printing) {

	GiNaC::symbol x("x"), y("y"), z("z");

	GiNaC::ex expression = GiNaC::sin(x + 2 / (y / x)) + 3 / z + 41;

	// check ginac expression
	std::string expected = "41+sin(x+2*y)+3*z";
	BOOST_CHECK_MESSAGE(expression.str() == expected, "got : " << expression.str() << " expected " << expected);

	// checks addition on ginac expression ?
	expected = "42+sin(x+2*y)+3*z";
	BOOST_CHECK_MESSAGE((expression + 1).str() == expected, "got : " << (expression + 1).str() << " expected " << expected);

	// checks foo.subs
	expected = "41+sin(2+2*y)+3*z";
	BOOST_CHECK_MESSAGE((expression.subs(x == 2)).str() == expected, "got : " << (expression.subs(x == 2)).str() << " expected " << expected);

	// ensure no effect of foo.subs on foo value
	expected = "41+sin(x+2*y)+3*z";
	BOOST_CHECK_MESSAGE(expression.str() == expected, "got : " << expression.str() << " expected " << expected);
}


BOOST_AUTO_TEST_CASE(t_ginac_expression_not_or_substitution) {

	GiNaC::symbol x("x"), y("y");
	GiNaC::ex expression;
	GiNaC::ex expected;

	expression = ginac_or(x, y).subs(x == GinacFactory::_TRUE_);
	expected = GinacFactory::_TRUE_;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_or(x, y).subs(x == GinacFactory::_FALSE_);
	expected = y;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_or(ginac_not(x), y).subs(x == GinacFactory::_TRUE_);
	expected = y;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_or(ginac_not(x), y).subs(x == GinacFactory::_FALSE_);
	expected = GinacFactory::_TRUE_;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());
}

BOOST_AUTO_TEST_CASE(t_ginac_expression_not_and_substitution) {

	GiNaC::symbol x("x"), y("y");
	GiNaC::ex expression;
	GiNaC::ex expected;

	expression = ginac_and(x, y).subs(x == GinacFactory::_TRUE_);
	expected = y;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_and(x, y).subs(x == GinacFactory::_FALSE_);
	expected = GinacFactory::_FALSE_;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_and(ginac_not(x), y).subs(x == GinacFactory::_TRUE_);
	expected = GinacFactory::_FALSE_;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());

	expression = ginac_and(ginac_not(x), y).subs(x == GinacFactory::_FALSE_);
	expected = y;
	BOOST_CHECK_MESSAGE(expression == expected, expression.str());
}

BOOST_AUTO_TEST_CASE(t_ginac_expression_and_or_composition_equivalence) {

	GiNaC::symbol x("x"), y("y"), z("z");
	GiNaC::ex expression;
	GiNaC::ex equivalent;

	expression = ginac_and(x, ginac_or(x, y));
	equivalent = ginac_or(x, ginac_and(x, y));
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());

	expression = ginac_and(x, ginac_or(x, y), z);
	equivalent = ginac_and(ginac_or(x, ginac_and(x, y)), z);
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());

	expression = ginac_and(x, ginac_or(ginac_not(x), y));
	equivalent = ginac_and(x, y);
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());

	expression = ginac_and(x, ginac_or(ginac_not(x), y), z);
	equivalent = ginac_and(x, y, z);
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());

	expression = ginac_and(ginac_not(x), ginac_or(ginac_not(x), y));
	equivalent = ginac_and(ginac_not(x), y);
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());

	expression = ginac_and(ginac_not(x), ginac_or(ginac_not(x), y), z);
	equivalent = ginac_and(ginac_not(x), y, z);
	BOOST_CHECK_MESSAGE(expression == equivalent, expression.str());
}

BOOST_AUTO_TEST_SUITE_END(); // FML



*/
