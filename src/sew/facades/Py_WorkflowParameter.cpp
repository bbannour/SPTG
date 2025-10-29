/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Py_WorkflowParameter.h"

namespace sep
{


bool Py_WorkflowParameter::load(const std::string & rawWorkflowParameters)
{
	return mWorkflowParameter.loadConfiguration(
			rawWorkflowParameters, "Pyversity");
}


std::string Py_WorkflowParameter::toString()
{
	if( mWorkflowParameter.hasParameterWObject() )
	{
		return mWorkflowParameter.getParameterWObject()->toString();
	}
	else
	{
		return "Empty Workflow Parameter";
	}
}

const WorkflowParameter& Py_WorkflowParameter::getWorkflowParameter() const{
	return mWorkflowParameter;
}

} /* namespace sep */
