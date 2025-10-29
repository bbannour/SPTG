/*
 * PyPort.h
 *
 *  Created on: 19 mars 2019
 *      Author: admin-local
 */

#ifndef FML_INFRASTRUCTURE_FACADES_PY_PORT_H_
#define FML_INFRASTRUCTURE_FACADES_PY_PORT_H_

#include <string>
#include <boost/python.hpp>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>
#include "fml/common/SpecifierElement.h"
#include <fml/infrastructure/Port.h>


namespace sep {

class Py_Port: public Port {
public:
	Py_Port(Machine * , std::string, const Modifier &);
	Py_Port(std::string );
	virtual ~Py_Port();
	inline const std::string getName() const {return NamedElement::getNameID();}
	inline bool isConnectablebleWith(Py_Port& other) const {return Port::isConnectablebleWith(other);};
	friend std::ostream& operator<<(std::ostream& o, const Py_Port& s) {return o << s.toString();}
};

} // End of namespace
#endif /* FML_INFRASTRUCTURE_FACADES_PY_PORT_H_ */
