
#ifndef PY_WORKFLOWPARAMETER_H_
#define PY_WORKFLOWPARAMETER_H_

#include <sew/WorkflowParameter.h>

namespace sep {


class Py_WorkflowParameter
{

protected:
	WorkflowParameter mWorkflowParameter;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Py_WorkflowParameter()
	: mWorkflowParameter( "PyversityWorkflowParameter" )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Py_WorkflowParameter()
	{
		//!! NOTHING
	}

	bool load(const std::string & rawWorkflowParameters);

	std::string toString();

	const WorkflowParameter& getWorkflowParameter() const;

};


} /* namespace sep */

#endif /* PY_WORKFLOWPARAMETER_H_ */
