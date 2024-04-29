/*
 * Py_Result.h
 *
 *  Created on: 15 mars 2019
 *      Author: admin-local
 */

#ifndef SEW_FACADES_PY_RESULT_H_
#define SEW_FACADES_PY_RESULT_H_

#include "fml/runtime/ExecutionContext.h"

#include <string>

namespace sep {

class Py_Engine;

class Py_Result
{

protected:
	/**
	 * ATTRIBUTES
	 */
	Py_Engine * executedEngine;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Py_Result(Py_Engine * engine = nullptr): executedEngine(engine) { }

	/**
	 * DESTRUCTOR
	 */
	virtual ~Py_Result() { };

	/**
	 * GETTERS
	 */
	const ExecutionContext& getResultExecutionGraph() const;

	/**
	 * SYMBOLIC EXECUTION GRAPH/TRACE DYSPLAYERS
	 */
	std::string display(bool showTransition = true,
			bool showCommunication = true, bool showAssign = false) const;

	std::string displayGraph(bool showTransition = true,
			bool showCommunication = true, bool showAssign = false) const;

	std::string displaySD(bool showAssign = false,
			bool showTransition = false, bool enabledNumerization = false) const;

	std::string displayUserText(bool showAssign = false,
			bool showTransition = false, bool enabledNumerization = false) const;

	std::string report() const;

};
}//end namespace

#endif /* SEW_FACADES_PY_RESULT_H_ */
