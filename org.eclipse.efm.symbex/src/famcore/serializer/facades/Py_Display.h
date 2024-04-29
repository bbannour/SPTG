
#ifndef PY_DISPLAY_H_
#define PY_DISPLAY_H_

#include <string>


namespace sep {

class ExecutionContext;
class Py_Engine;
class System;


class Py_Display  {

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Py_Display()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Py_Display()
	{
		//!! NOTHING
	}

	// Default display <=> displaySTS
	std::string display(const System & aSystem, bool showStatement = true,
			bool showCommunication = true, bool showAssign = true);

	// Display Symbolic Transition System
	std::string displaySTS(Py_Engine & engine, const System & aSystem,
			bool showStatement = true,
			bool showCommunication = true, bool showAssign = true);

	// Display Symbolic Execution Graph
	std::string displaySymbexGraph(
			Py_Engine & engine, const ExecutionContext & anEC,
			bool showTransition, bool showCommunication, bool showAssign);

	// Display Symbolic Execution Trace as Sequence Diagram
	std::string displaySymbexSD(
			Py_Engine & engine, const ExecutionContext & anEC,
			bool showAssign, bool showTransition, bool enabledNumerization);

	// Display Symbolic Execution Trace as User Textual Defined Format
	std::string displaySymbexUserText(Py_Engine & engine,
			const ExecutionContext & anEC,
			bool showAssign, bool showTransition, bool enabledNumerization);

	// Display InteractionStructure view
	std::string displayCommunicationGraph(const System& aSystem);
};


} /* namespace sep */

#endif /* PY_DISPLAY_H_ */
