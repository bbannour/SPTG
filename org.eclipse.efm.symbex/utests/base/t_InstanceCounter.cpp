/*
 *   Unit test of InstanceCounter class
 */


#include <iostream>
#include <string>

#include "boost/test/unit_test.hpp"

#include "printer/OutStream.h"
#include "base/InstanceCounter.h"


using namespace std;
using namespace sep;


// Local fixtures
OutStream os(&cout);
class A : public InstanceCounter<A> {};            // Regular case
class B : public A {};                             // To see what happens with heritage
class C : public A, public InstanceCounter<C> {};  // To see what happens with multiple heritage


BOOST_AUTO_TEST_SUITE(Base);

BOOST_AUTO_TEST_CASE(t_InstanceCounter_all) {
	// Due to the nature of the tested mechanism (instance counting), we are unable to create
	// multiple independent unit test cases (as we should have been)
	// Hence all assertions are checked within the same big test case

	A::showCounters(os, "A");

    // No instance created
	BOOST_CHECK(A::INSTANCE_ALIVE == 0);
	BOOST_CHECK(A::INSTANCE_CREATED == 0);

	// Instance created as an automatic variable
	A a1;
	a1.showCounters(os, "A");
	BOOST_CHECK(a1.INSTANCE_ALIVE == 1);
	BOOST_CHECK(a1.INSTANCE_CREATED == 1);

	// Instance created as an automatic variable in a subblock ...
	{
		A a2;
		a2.showCounters(os, "A");
		BOOST_CHECK(a2.INSTANCE_ALIVE == 2);
		BOOST_CHECK(a2.INSTANCE_CREATED == 2);
	}
    // ... should be automatically deleted outside the block
	a1.showCounters(os, "A");
	BOOST_CHECK(a1.INSTANCE_ALIVE == 1);
	BOOST_CHECK(a1.INSTANCE_CREATED == 2);

	// Reference on existing instance
	A& ra1 = a1;
	a1.showCounters(os, "A");
	BOOST_CHECK(ra1.INSTANCE_ALIVE == 1);
	BOOST_CHECK(ra1.INSTANCE_CREATED == 2);
	BOOST_CHECK(a1.INSTANCE_ALIVE == ra1.INSTANCE_ALIVE);
	BOOST_CHECK(a1.INSTANCE_CREATED == ra1.INSTANCE_CREATED);

	// Pointer on existing instance
	A* pa1 = &a1;
	a1.showCounters(os, "A");
	BOOST_CHECK(pa1->INSTANCE_ALIVE == 1);
	BOOST_CHECK(pa1->INSTANCE_CREATED == 2);
	BOOST_CHECK(a1.INSTANCE_ALIVE == pa1->INSTANCE_ALIVE);
	BOOST_CHECK(a1.INSTANCE_CREATED == pa1->INSTANCE_CREATED);

	// Instance created on the heap ...
	A* pa3 = new A();
	pa3->showCounters(os, "A");
	BOOST_CHECK(pa3->INSTANCE_ALIVE == 2);
	BOOST_CHECK(pa3->INSTANCE_CREATED == 3);
	// ... then deleted
	delete pa3;
	a1.showCounters(os, "A");
	BOOST_CHECK(a1.INSTANCE_ALIVE == 1);
	BOOST_CHECK(a1.INSTANCE_CREATED == 3);

	// Counting mecanism should works through heritage relations
	B b;   // Remind : B is a A
	b.showCounters(os, "B");
	BOOST_CHECK(b.INSTANCE_ALIVE == 2);
	BOOST_CHECK(b.INSTANCE_CREATED == 4);

	// and through upcast
	A a4 = (A) b; // Upcast changes nothing
	a4.showCounters(os, "A");
	BOOST_CHECK(a4.INSTANCE_ALIVE == 2);
	BOOST_CHECK(a4.INSTANCE_CREATED == 4);

	// What happens with multiple heritage
	C c;
	// c.showCounters(cout, "C"); // Doesn't compile due to the ambiguity of showCounters() in the multiple heritage (normal)
	// In this case we have to choose which counter we want to query :
	c.InstanceCounter<C>::showCounters(os, "C"); // C: 1/1
	c.InstanceCounter<A>::showCounters(os, "A"); // A: 3/5
	BOOST_CHECK(c.InstanceCounter<C>::INSTANCE_ALIVE == 1);
	BOOST_CHECK(c.InstanceCounter<C>::INSTANCE_CREATED == 1);
	BOOST_CHECK(c.InstanceCounter<A>::INSTANCE_ALIVE == 3);
	BOOST_CHECK(c.InstanceCounter<A>::INSTANCE_CREATED == 5);
}

BOOST_AUTO_TEST_SUITE_END(); // BASE

