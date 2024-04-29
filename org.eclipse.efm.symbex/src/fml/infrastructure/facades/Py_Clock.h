/*
 * Py_Clock.h
 *
 *  Created on: 15 avr. 2019
 *      Author: admin-local
 */

#ifndef FML_INFRASTRUCTURE_FACADES_PY_CLOCK_H_
#define FML_INFRASTRUCTURE_FACADES_PY_CLOCK_H_

#include <string>

#include "fml/infrastructure/Machine.h"
#include "fml/infrastructure/Variable.h"
#include "fml/type/TypeManager.h"

namespace sep {


class Py_Clock: public Variable {

public:
	Py_Clock(Machine* m, std::string name):
	  Variable(m, Modifier::NATURE_VARIABLE_KIND, TypeManager::getPrimitiveType("clock"), name)
	  {}

	Py_Clock(std::string name):
	  Variable(nullptr, Modifier::NATURE_VARIABLE_KIND, TypeManager::getPrimitiveType("clock"), name)
	  {}

	   inline const std::string getName() const {return NamedElement::getNameID();}

	   inline friend std::ostream& operator<<(std::ostream& o, const Py_Clock& v) {
		   OutStream out(o);
		   v.strHeader(out);
		   return o;
		}

};

} // end of namespace

#endif /* FML_INFRASTRUCTURE_FACADES_PY_CLOCK_H_ */
