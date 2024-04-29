
#include <boost/python.hpp>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>

#include <filesystem>
#include <iostream>
#include <string>

#include "fml/infrastructure/System.h"
#include "famcore/serializer/facades/Py_Display.h"
#include "fml/infrastructure/facades/Py_Const.h"
#include "fml/infrastructure/facades/Py_Clock.h"
#include "fml/infrastructure/facades/Py_Const.h"
#include "fml/infrastructure/facades/Py_Port.h"
#include "fml/infrastructure/facades/Py_Variable.h"
#include "fml/infrastructure/facades/Py_State.h"
#include "fml/infrastructure/facades/Py_StateMachine.h"
#include "fml/infrastructure/facades/Py_Transition.h"
#include "fml/infrastructure/facades/Py_System.h"
#include "fml/infrastructure/System.h"
#include "sew/facades/Py_WorkflowParameter.h"
#include "sew/facades/Py_Engine.h"
#include "sew/facades/Py_Result.h"
#include <util/avm_assert.h>
//for init()
#include <base/ClassKindInfo.h>
#include <builder/Builder.h>
#include <builder/Loader.h>
#include <computer/EnvironmentFactory.h>
//#include  <famcore/api/ProcessorUnitRepository.h>
#include <fml/executable/ExecutableLib.h>
#include <fml/expression/ExpressionFactory.h>
#include <fml/runtime/RuntimeLib.h>
#include <util/avm_vfs.h>
#include <fml/lib/AvmLang.h>

using namespace std;
using namespace boost::python;
using namespace sep;

static void initialize(){
	VFS::LaunchPath = std::filesystem::current_path().string();
	ClassKindInfoInitializer::load();
	OutStream::load();    
	XLIA_SYNTAX::load();
	ExpressionFactory::load();
	TypeManager::load();
	EnvironmentFactory::load();
	Builder::load();
	ExecutableLib::load();
	RuntimeLib::load();
}

void diversityError_translator(DiversityError const& e) {
    PyErr_SetString(PyExc_RuntimeError, (string("DiversityError: ") + string(e.what())).c_str());
}

void avmExitError_translator(AvmExitException  const& e) {
    PyErr_SetString(PyExc_RuntimeError, (string("AvMExitError: ") + string(e.what())).c_str());
}

BOOST_PYTHON_MODULE(maatcore) {

	def("initialize", &initialize);

	register_exception_translator<DiversityError>(diversityError_translator);
	register_exception_translator<AvmExitException>(avmExitError_translator);


	///////////////////////////////////////////////////////////////////////////
	// UTILS - HELPERS
	///////////////////////////////////////////////////////////////////////////

	class_<vector<string> >("string_vector")
		.def(vector_indexing_suite< vector<string> >())
		;

	class_<vector<int> >("int_vector")
		.def(vector_indexing_suite< vector<int> >())
		;

	class_<vector<Py_Port*> >("port_vector")
		.def(vector_indexing_suite< vector<Py_Port*> >())
		;

    class_<System>("Base_System",init<string>())
    	;


	///////////////////////////////////////////////////////////////////////////
	// SYSTEM COMPONENT & DISPLAYER
	///////////////////////////////////////////////////////////////////////////

	class_<Py_System, bases<System>>("Py_System", init<string, string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_System::getName)
		.def("addStateMachine", &Py_System::addStateMachine, return_value_policy<reference_existing_object>())
		.def("getPortNames", &Py_System::getPortNames)
		.def("getMachineNames", &Py_System::getMachineNames)
		.def("connect", &Py_System::connect)
		;

	class_<Py_Display>("Py_Display", init<>())
		.def("display", &Py_Display::display)
		.def("displayCommunicationGraph", &Py_Display::displayCommunicationGraph)
		;

	///////////////////////////////////////////////////////////////////////////
	// STATEMACHINE COMPONENT
	///////////////////////////////////////////////////////////////////////////

	class_<Py_StateMachine>("Py_StateMachine", init<string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_StateMachine::getName)
		.def("getStateNames", &Py_StateMachine::getStateNames)
		.def("getPortNames", &Py_StateMachine::getPortNames)
		.def("addState", &Py_StateMachine::addState, return_value_policy<reference_existing_object>())
		.def("addInitialState", &Py_StateMachine::addInitialState, return_value_policy<reference_existing_object>())
		.def("addFinalState", &Py_StateMachine::addFinalState, return_value_policy<reference_existing_object>())
		.def("addStartState", &Py_StateMachine::addStartState, return_value_policy<reference_existing_object>())
		.def("addTerminalState", &Py_StateMachine::addTerminalState, return_value_policy<reference_existing_object>())
		.def("addJunctionState", &Py_StateMachine::addJunctionState, return_value_policy<reference_existing_object>())
		.def("addChoiceState", &Py_StateMachine::addChoiceState, return_value_policy<reference_existing_object>())
		.def("addAndState", &Py_StateMachine::addAndState, return_value_policy<reference_existing_object>())
		.def("addOrState", &Py_StateMachine::addOrState, return_value_policy<reference_existing_object>())
		.def("addInPort", &Py_StateMachine::addInPort, return_value_policy<reference_existing_object>())
		.def("addOutPort", &Py_StateMachine::addOutPort, return_value_policy<reference_existing_object>())
		.def("addVar", &Py_StateMachine::addVar, return_value_policy<reference_existing_object>())
		.def("addClock", &Py_StateMachine::addClock, return_value_policy<reference_existing_object>())
		.def("addConst", &Py_StateMachine::addConst, return_value_policy<reference_existing_object>())
		;

	///////////////////////////////////////////////////////////////////////////
	// CONTROL STATE ELEMENTS : STATE - PSEUDOSTATE
	///////////////////////////////////////////////////////////////////////////

	class_<Py_BaseState>("Py_TransitionableState", init<string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_BaseState::getName)
		.def("addTransition", &Py_BaseState::addTransition, return_value_policy<reference_existing_object>())
		;

	class_<Py_State, bases<Py_BaseState>>("Py_State", init<string>())
		;

	class_<Py_InitialState, bases<Py_BaseState>>("Py_InitialState", init<string>())
		.def("isInitial", &Py_InitialState::isInitial)
		;

	class_<Py_FinalState, bases<Py_BaseState>>("Py_FinalState", init<string>());

	class_<Py_StartState, bases<Py_BaseState>>("Py_StartState", init<string>());

	class_<Py_TerminalState, bases<Py_BaseState>>("Py_TerminalState", init<string>());

	class_<Py_JunctionState, bases<Py_BaseState>>("Py_JunctionState", init<string>());

	class_<Py_ChoiceState, bases<Py_BaseState>>("Py_ChoiceState", init<string>());

	class_<Py_AndState>("Py_AndState", init<string>())
		.def("addAndState", &Py_AndState::addAndState, return_value_policy<reference_existing_object>())
		.def("addOrState", &Py_AndState::addOrState, return_value_policy<reference_existing_object>())
		;

	class_<Py_OrState>("Py_OrState", init<string>())
		.def("addState", &Py_OrState::addState, return_value_policy<reference_existing_object>())
		.def("addAndState", &Py_OrState::addAndState, return_value_policy<reference_existing_object>())
		.def("addOrState", &Py_OrState::addOrState, return_value_policy<reference_existing_object>())
		.def("addStartState", &Py_OrState::addStartState, return_value_policy<reference_existing_object>())
		.def("addFinalState", &Py_OrState::addFinalState, return_value_policy<reference_existing_object>())
		.def("addInitialState", &Py_OrState::addInitialState, return_value_policy<reference_existing_object>())
		.def("addJunctionState", &Py_OrState::addJunctionState, return_value_policy<reference_existing_object>())
		.def("addChoiceState", &Py_OrState::addChoiceState, return_value_policy<reference_existing_object>())
		.def("addTerminalState", &Py_OrState::addTerminalState, return_value_policy<reference_existing_object>())
		;

	///////////////////////////////////////////////////////////////////////////
	// BEHAVIORAL ELEMENT : TRANSITION
	///////////////////////////////////////////////////////////////////////////

	class_<Py_Transition>("Py_Transition", init<string, Py_BaseState&, Py_BaseState& >())
		.def(self_ns::str(self))
		.def("__repr__", &Py_Transition::getName)
		.def("addReceive", &Py_Transition::addReceive)
		.def("addSend", &Py_Transition::addSend)
		.def("addGuard", &Py_Transition::addGuard)
		.def("addClockGuard", &Py_Transition::addClockGuard)
		.def("addStatement", &Py_Transition::addStatement)
		;


	///////////////////////////////////////////////////////////////////////////
	// PROPERTY ELEMENT
	///////////////////////////////////////////////////////////////////////////
	
	// PORT
	class_<Py_Port>("Py_Port", init<string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_Port::getName)
		.def("isConnectablebleWith", &Py_Port::isConnectablebleWith)
		;

	// CLOCK VARIABLE for TIMED MACHINE
	class_<Py_Clock>("Py_Clock", init<string>())
		.def(self_ns::str(self))
		;

	// VARIABLE
	class_<Py_Variable>("Py_Variable", init<string,string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_Variable::getName)
		.def(self + self)
		.def(self - self)
		.def(self * self)
		.def(self / self)
		.def(self + string())
		.def(self - string())
		.def(self * string())
		.def(self / string())
		.def(string() + self)
		.def(string() - self)
		.def(string() * self)
		.def(string() / self)
		.def(self + int())
		.def(self - int())
		.def(self * int())
		.def(self / int())
		.def(int() + self)
		.def(int() - self)
		.def(int() * self)
		.def(int() / self)
		.def<void (Py_Variable::*)(int)>("setIntInitVal", &Py_Variable::setInitVal)
		.def<void (Py_Variable::*)(bool)>("setBoolInitVal", &Py_Variable::setInitVal)
		.def<void (Py_Variable::*)(float)>("setFloatInitVal", &Py_Variable::setInitVal)
		.def<void (Py_Variable::*)(std::string)>("setStringInitVal", &Py_Variable::setInitVal)
		;

	// CONST VARIABLE
	class_<Py_Const>("Py_Const", init<string,string>())
		.def(self_ns::str(self))
		.def("__repr__", &Py_Const::getName)
		.def<void (Py_Const::*)(int)>("setIntVal", &Py_Const::setVal)
		.def<void (Py_Const::*)(bool)>("setBoolVal", &Py_Const::setVal)
		.def<void (Py_Const::*)(float)>("setFloatVal", &Py_Const::setVal)
		.def<void (Py_Const::*)(std::string)>("setStringVal", &Py_Const::setVal)
		;


	///////////////////////////////////////////////////////////////////////////
	// WORKFLOW COMPONENT : ENGINE - PARAMETERS - RESULT 
	///////////////////////////////////////////////////////////////////////////

	class_<Py_Engine>("Py_Engine", init<Py_WorkflowParameter&>())
		.def("start", &Py_Engine::startEngine)
		.def("setSystem", &Py_Engine::setSystem)
		;

	class_<Py_WorkflowParameter>("Py_WorkflowParameter", init<>())
		.def("load", &Py_WorkflowParameter::load)
		;

	class_<Py_Result>("Py_Result",init<>())
		.def("report", &Py_Result::report)
		.def("display", &Py_Result::display)
		.def("displayGraph", &Py_Result::displayGraph)
		.def("displaySD", &Py_Result::displaySD)
		.def("displayText", &Py_Result::displayUserText)
		;


}
