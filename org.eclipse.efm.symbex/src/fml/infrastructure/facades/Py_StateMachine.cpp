/*
 * Py_StateMachine.cpp
 *
 *  Created on: 19 mars 2019
 *      Author: admin-local
 */

#include <stdexcept>

#include "fml/infrastructure/facades/Py_StateMachine.h"
#include "fml/infrastructure/facades/Py_Clock.h"
#include "fml/infrastructure/facades/Py_Const.h"
#include "fml/infrastructure/facades/Py_State.h"
#include "fml/infrastructure/facades/Py_Port.h"
#include "fml/infrastructure/facades/Py_Variable.h"
#include "fml/common/SpecifierElement.h"


using namespace sep;

	Py_State & Py_StateMachine::addState(const std::string & name) {
		Py_State * state = new Py_State(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_InitialState& Py_StateMachine::addInitialState(const std::string & name) {
		Py_InitialState * state = new Py_InitialState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_FinalState& Py_StateMachine::addFinalState(const std::string & name) {
		Py_FinalState * state = new Py_FinalState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_StartState& Py_StateMachine::addStartState(const std::string & name) {
		Py_StartState * state = new Py_StartState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_TerminalState& Py_StateMachine::addTerminalState(const std::string & name) {
		Py_TerminalState * state = new Py_TerminalState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_JunctionState& Py_StateMachine::addJunctionState(const std::string & name) {
		Py_JunctionState * state = new Py_JunctionState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_ChoiceState& Py_StateMachine::addChoiceState(const std::string & name) {
		Py_ChoiceState * state = new Py_ChoiceState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_AndState& Py_StateMachine::addAndState(const std::string & name) {
		Py_AndState * state = new Py_AndState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_OrState& Py_StateMachine::addOrState(const std::string & name) {
		Py_OrState * state = new Py_OrState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	Py_Port& Py_StateMachine::addInPort(const std::string & name, boost::python::list & param_types) {
		return Py_StateMachine::addPort(name, param_types,Modifier::PROPERTY_INPUT_DIRECTION);
	}

	Py_Port& Py_StateMachine::addOutPort(const std::string & name, boost::python::list & param_types) {
		return Py_StateMachine::addPort(name, param_types,Modifier::PROPERTY_OUTPUT_DIRECTION);
	}

	Py_Port& Py_StateMachine::addPort(const std::string & name, boost::python::list & param_types, Modifier& mod) {
		Py_Port * port = new Py_Port(this, name, mod);
		std::string current_param_type;
		while(boost::python::len(param_types) > 0) {
			current_param_type = boost::python::extract<std::string>(param_types.pop(0));
			const TypeSpecifier & current_ts = TypeManager::getPrimitiveType(current_param_type);
			if (not current_ts.valid()) {
				throw std::exception(); //FIXME : define specific exception
			}
			else {
			    port->appendParameter(current_ts);
			}
		}
		Machine::saveOwnedElement(port);
		return *port;
	}

	Py_Variable & Py_StateMachine::addVar(const std::string& varName, const std::string& typeName ){
		Py_Variable* var= new Py_Variable(this, varName,typeName);
		Machine::saveOwnedElement(var);
		return *var;
	}

	Py_Const & Py_StateMachine::addConst(const std::string& varName, const std::string& typeName ){
		Py_Const* con = new Py_Const(this, varName, typeName);
		Machine::saveOwnedElement(con);
		return *con;
	}


	Py_Clock & Py_StateMachine::addClock(const std::string& clockName) {
		Py_Clock* clock = new Py_Clock(this, clockName);
		Machine::saveOwnedElement(clock);
		return *clock;
	};


