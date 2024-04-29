#include <string>

#include "fml/infrastructure/Transition.h"
#include "fml/infrastructure/facades/Py_State.h"
#include "fml/infrastructure/facades/Py_Transition.h"
#include "fml/infrastructure/facades/Py_Port.h"

using namespace sep;

Py_Transition::Py_Transition(std::string name, Py_BaseState& source, Py_BaseState& target):
				  Transition(source, name, target) {std::string a;}

bool Py_Transition::addSend(Py_Port & outPort, boost::python::list& rvalues){
	std::vector <std::string> actualrvalues = std::vector <std::string>();
	while(boost::python::len(rvalues) > 0) {
		actualrvalues.push_back(boost::python::extract<std::string>(rvalues.pop(0)));
	}
	return Transition::addOutput(outPort,actualrvalues);
}

bool Py_Transition::addReceive(Py_Port & inPort, boost::python::list& lvalues){
	std::vector <std::string> actuallvalues = std::vector <std::string>();
	while(boost::python::len(lvalues) > 0) {
		actuallvalues.push_back(boost::python::extract<std::string>(lvalues.pop(0)));
	}
	return Transition::addInput(inPort,actuallvalues);
}

bool Py_Transition::addGuard(const std::string& g) {
	return Transition::addStatement("guard (" + g + ")");
};

bool Py_Transition::addClockGuard(const std::string& cg) {
	return Transition::addStatement("tguard (" + cg + ")");
};

bool Py_Transition::addStatement(const std::string& s) {
	return Transition::addStatement(s);
}
