#ifndef STATE_H_
#define STATE_H_

#include <string>

#include "common/GeneralException.h"
#include "common/NamedElement.h"
#include "fml/infrastructure/BehavioralPart.h"
#include "fml/infrastructure/Machine.h"
#include "fml/infrastructure/facades/Py_Transition.h"
#include "fml/common/SpecifierElement.h"

namespace sep {
  

class Py_BaseState: public Machine {

public:  
  Py_BaseState(std::string name): 
  Machine(nullptr, name, Specifier::EXECUTABLE_UNDEFINED_SPECIFIER) {}

  Py_BaseState(Machine* container, std::string name, Specifier spec): 
  Machine(container, name, spec) {}

  inline Py_Transition & addTransition(std::string name, Py_BaseState& target) {
	  if(target.isInitial() or target.isStart()) {throw DiversityError("Start or Initial state cannot be the target of a transition");}
    Py_Transition* transition = new Py_Transition(name, *this, target);
    this->getUniqBehaviorPart()->saveOutgoingTransition( transition );
    return (*transition);
	}
  
  inline const std::string getName() const {return NamedElement::getNameID();}
  
  friend std::ostream& operator<< (std::ostream& o, const Py_BaseState& bs) {
		return o << bs.toString();
	}

  inline virtual bool isInitial() const {return false;}
  inline virtual bool isStart() const {return false;}
  inline virtual bool isFinal() const {return false;}
  inline virtual bool isTerminal() const {return false;}
  inline virtual bool isJunction() const {return false;}
  inline virtual bool isChoice() const {return false;}
  inline virtual bool isAnd() const {return false;}
  inline virtual bool isOr() const {return false;}

};


class Py_State: public Py_BaseState {

public:
	Py_State(std::string name): 
  Py_BaseState(name) 
  {this->setSpecifier(Specifier::EXECUTABLE_STATE_SPECIFIER);}

	Py_State(Machine * container, std::string name): 
  Py_BaseState(container, name, Specifier::EXECUTABLE_STATE_SPECIFIER) 
  {}
  
};


class Py_InitialState: public Py_BaseState {
  
public:
	Py_InitialState(std::string name): 
  Py_BaseState(name) 
  {this->setSpecifier(Specifier::EXECUTABLE_PSEUDOSTATE_INITIAL_SPECIFIER);}

	Py_InitialState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_PSEUDOSTATE_INITIAL_SPECIFIER) 
  {}

	inline bool isInitial() const {return true;}

};


class Py_FinalState: public Py_BaseState {
  
public:

	Py_FinalState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_STATE_FINAL_SPECIFIER);}

	Py_FinalState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_STATE_FINAL_SPECIFIER) 
  {}

};


class Py_StartState: public Py_BaseState {
  
public:

	Py_StartState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_STATE_START_SPECIFIER);}

	Py_StartState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_STATE_START_SPECIFIER) 
  {}

    inline bool isStart() const {return true;}

};

class Py_TerminalState: public Py_BaseState {
  
public:

	Py_TerminalState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_PSEUDOSTATE_TERMINAL_SPECIFIER);}
  
	Py_TerminalState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_PSEUDOSTATE_TERMINAL_SPECIFIER) 
  {}

	inline bool isTerminal() const {return true;}

};


class Py_JunctionState: public Py_BaseState {
  
public:

	Py_JunctionState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_PSEUDOSTATE_JUNCTION_SPECIFIER);}

	Py_JunctionState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_PSEUDOSTATE_JUNCTION_SPECIFIER) 
  {}

};


class Py_ChoiceState: public Py_BaseState {
  
public:

	Py_ChoiceState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_PSEUDOSTATE_CHOICE_SPECIFIER);}

	Py_ChoiceState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_PSEUDOSTATE_CHOICE_SPECIFIER) 
  {}

	inline bool isChoice() const {return true;}


};


class Py_OrState;

class Py_AndState: public Py_BaseState {
  
public:

	Py_AndState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_STATE_AND_SPECIFIER);}

	Py_AndState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_STATE_AND_SPECIFIER) 
  {}

	inline Py_AndState & addAndState(std::string name) {
		Py_AndState * state = new Py_AndState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_OrState & addOrState(std::string name);

	inline bool isAnd() const {return true;}

  
  //inline std::vector< std::string> getStateNames() const {return MachineQuery::getStateNames();}

};


class Py_OrState: public Py_BaseState {
  
public:

	Py_OrState(std::string name):
  Py_BaseState(name)
  {this->setSpecifier(Specifier::EXECUTABLE_STATE_OR_SPECIFIER);}

	Py_OrState(Machine * container, std::string name):
  Py_BaseState(container, name, Specifier::EXECUTABLE_STATE_OR_SPECIFIER) 
  {}

	inline std::string getName() {return NamedElement::getNameID();}

	inline bool isOr() const {return true;}

	inline Py_AndState & addAndState(const std::string name) {
		Py_AndState * state = new Py_AndState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_OrState & addOrState(const std::string name) {
		Py_OrState * state = new Py_OrState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_State & addState(const std::string name) {
		Py_State * state = new Py_State(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_StartState & addStartState(const std::string name) {
		Py_StartState * state = new Py_StartState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_FinalState & addFinalState(const std::string name) {
		Py_FinalState * state = new Py_FinalState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_InitialState & addInitialState(const std::string name) {
		Py_InitialState * state = new Py_InitialState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_JunctionState & addJunctionState(const std::string name) {
		Py_JunctionState * state = new Py_JunctionState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_ChoiceState &addChoiceState(const std::string name) {
		Py_ChoiceState * state = new Py_ChoiceState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Py_TerminalState & addTerminalState(const std::string name) {
		Py_TerminalState * state = new Py_TerminalState(this, name);
		Machine::saveOwnedElement(state);
		return( *state );
	}

	inline Transition & addTransition(std::string name) {
		Transition * transition = new Transition(*this, name);
		this->getUniqBehaviorPart()->saveOutgoingTransition( transition );
		return( *transition );
	}
};

inline Py_OrState & Py_AndState::addOrState(const std::string name) {
	Py_OrState * state = new Py_OrState(this, name);
	Machine::saveOwnedElement(state);
  return( *state );
 }

} /* namespace sep */

#endif /* STATE_H_ */
