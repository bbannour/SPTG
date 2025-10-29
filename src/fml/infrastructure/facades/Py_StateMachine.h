
#ifndef STATEMACHINE_H_
#define STATEMACHINE_H_

#include <boost/python.hpp>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>
#include <string>
#include <vector>



#include "common/NamedElement.h"
#include "fml/infrastructure/Machine.h"
#include "fml/common/SpecifierElement.h"


#include "fml/type/TypeManager.h"

namespace sep {

class Py_Clock;
class Py_Const;
class Py_State;
class Py_InitialState;
class Py_FinalState;
class Py_StartState;
class Py_TerminalState;
class Py_JunctionState;
class Py_ChoiceState;
class Py_AndState;
class Py_OrState;
class Py_Port;
class Py_Variable;

class Py_StateMachine: public Machine {
public:
	Py_StateMachine(std::string name)
	: Machine(nullptr, name, Specifier::EXECUTABLE_STATEMACHINE_SPECIFIER) {}

	Py_StateMachine(Machine* system, std::string name)
	: Machine(system, name, Specifier::EXECUTABLE_STATEMACHINE_SPECIFIER) {}

	inline const std::string getName() const {return NamedElement::getNameID();}
  
	inline std::vector<std::string> getStateNames() const {return Machine::getStateNames();}

	Py_State & addState(const std::string &);

	Py_InitialState & addInitialState(const std::string &);
  
	Py_FinalState & addFinalState(const std::string & );
  
 	Py_StartState & addStartState(const std::string & );

	Py_TerminalState & addTerminalState(const std::string & );
  
	Py_JunctionState & addJunctionState(const std::string & );

	Py_ChoiceState & addChoiceState(const std::string & );
  
	Py_AndState & addAndState(const std::string & );

	Py_OrState & addOrState(const std::string & );

	Py_Port & addInPort(const std::string & , boost::python::list & );

	Py_Port & addOutPort(const std::string & , boost::python::list & );

	Py_Variable & addVar(const std::string&, const std::string&);

	Py_Const & addConst(const std::string&, const std::string&);

	Py_Clock & addClock(const std::string&);

private:
	Py_Port & addPort(const std::string & , boost::python::list &, Modifier&);

	friend std::ostream& operator<< (std::ostream& o, const Py_StateMachine& sm) {
		return o << sm.toString();
	}

};


} /* namespace sep */

#endif /* STATEMACHINE_H_ */
