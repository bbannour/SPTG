/*
 * PyEngine.h
 *
 *  Created on: 4 mars 2019
 *      Author: xavier
 */

#ifndef SEW_FACADES_PY_ENGINE_H_
#define SEW_FACADES_PY_ENGINE_H_

#include "common/GeneralException.h"
#include "sew/SymbexEngine.h"
#include "sew/facades/Py_WorkflowParameter.h"
#include "sew/WorkflowParameter.h"
#include "fml/workflow/WObject.h"
#include "Py_Result.h"

namespace sep
{


class Py_Engine : public SymbexEngine {

public:

	Py_Engine(Py_WorkflowParameter& wfParam):
  SymbexEngine(wfParam.getWorkflowParameter().getEngineWObject()) {}
  
  Py_Engine(const WObject* wo): SymbexEngine(wo) {}

  Py_Engine(const Py_Engine& other): Py_Engine(other.getParameterWObject()) {
    /*FIXME (POSSIBLY?) : this is a shallow copy, not a deep copy
     * Needed by boost python due to AVM_DECLARE_UNCLONABLE_CLASS(SymbexEngine) 
     * in SymbexEngine.h
     * */
    }

	~Py_Engine(){}

//	void setParam(const Py_WorkflowParameter wfParam) {};

	Py_Result startEngine();

	bool setSystem(System&);

};

} //namespace sep
#endif /* SEW_FACADES_PY_ENGINE_H_ */
