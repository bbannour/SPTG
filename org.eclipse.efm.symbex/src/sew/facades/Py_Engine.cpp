/*
 * PyEngine.cpp
 *
 *  Created on: 4 mars 2019
 *      Author: xavier
 */



#include <sew/facades/Py_Engine.h>
#include "sew/SymbexEngine.h"
#include "fml/template/TemplateFactory.h"
#include <printer/OutStream.h>

using namespace sep;

Py_Result Py_Engine::startEngine(){
    bool ok(true);
    ok = ok and configure();
    ok = ok and startComputing();

    return Py_Result(this);
}


bool Py_Engine::setSystem(System& s) {
	TemplateFactory::genProperty(&s);
	TemplateFactory::genBehavior(&s);

	mConfiguration.setSpecification(&s);
	bool isOK = mConfiguration.hasSpecification();
	return isOK;
}
