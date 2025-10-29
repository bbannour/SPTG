/*
 * PyPort.cpp
 *
 *  Created on: 19 mars 2019
 *      Author: admin-local
 */


#include <boost/python.hpp>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>

#include <fml/infrastructure/facades/Py_Port.h>
#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Port.h>

using namespace sep;

Py_Port::Py_Port(Machine* machine, std::string name, const Modifier & mod):
	Port(machine->getPropertyPart(), name, IComPoint::IO_PORT_NATURE, mod) {
	getwModifier().setVisibilityPublic();
}

Py_Port::Py_Port(std::string name):
	Port(nullptr, name, IComPoint::IO_PORT_NATURE, Modifier::PROPERTY_INOUT_DIRECTION) {
	getwModifier().setVisibilityPublic();
}

Py_Port::~Py_Port() {
	// TODO Auto-generated destructor stub
}

