#ifndef PY_TRANSITION_H_
#define PY_TRANSITION_H_


#include <string>
#include <vector>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>
#include <boost/python.hpp>

namespace sep {

class Py_Port;
class Py_BaseState;

class Py_Transition: public Transition {

public:
	Py_Transition(std::string name, Py_BaseState&, Py_BaseState&);

	inline const std::string getName() const {return NamedElement::getNameID();}

	bool addSend(Py_Port & outPort, boost::python::list& rvalues);

	bool addReceive(Py_Port & inPort, boost::python::list& rvalues);

	bool addGuard(const std::string&);

	bool addClockGuard(const std::string&);

	bool addStatement(const std::string&);

	friend std::ostream& operator<< (std::ostream& o, const Py_Transition& t) {
		return o << t.toString();
	}


};

}

#endif // PY_TRANSITION_H_
