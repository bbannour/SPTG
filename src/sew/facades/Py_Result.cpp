/*
 * Py_Result.cpp
 *
 *  Created on: 15 mars 2019
 *      Author: admin-local
 */

#include <sew/facades/Py_Result.h>
#include <sew/facades/Py_Engine.h>
#include  <famcore/serializer/facades/Py_Display.h>

using namespace sep;


static std::string errorMessage(const std::string & message)
{
	StringOutStream oss;
	oss << "@startuml\n"
		<< "(*) --> \""
		<< "<b><size:20><color:red>" << message << "</color></size></b>\"\n"
		<< "@enduml";

	return oss.str();
}

static std::string errorMessageSD(const std::string & message)
{
	StringOutStream oss;
	oss << "@startuml\n"
		<< "note over Error\n"
		<< "\t<b><size:20><color:red>" << message << "</color></size></b>\n"
		<< "end note\n"
		<< "@enduml";

	return oss.str();
}


const ExecutionContext& Py_Result::getResultExecutionGraph() const{
	return (executedEngine != nullptr)
			? executedEngine->getConfiguration().getFirstExecutionTrace()
			: ExecutionContext::nullref();
}

/**
 * EXECUTION REPORTERS
 */
std::string Py_Result::display(bool showTransition,
		bool showCommunication, bool showAssign) const
{
	if( executedEngine != nullptr )
	{
		Py_Display displayer;

		return displayer.displaySymbexGraph(*executedEngine,
				getResultExecutionGraph(),
				showTransition, showCommunication, showAssign);
	}

	return errorMessage("NO DISPLAY: INVALID EXECUTED ENGINE !");
}


std::string Py_Result::displayGraph(bool showTransition,
		bool showCommunication, bool showAssign) const
{
	if( executedEngine != nullptr )
	{
		Py_Display displayer;

		return displayer.displaySymbexGraph(*executedEngine,
				getResultExecutionGraph(),
				showTransition, showCommunication, showAssign);
	}

	return errorMessage("NO DISPLAY: INVALID EXECUTED ENGINE !");
}

std::string Py_Result::displaySD(bool showAssign,
		bool showTransition, bool enabledNumerization) const
{
	if( executedEngine != nullptr )
	{
		Py_Display displayer;

		return displayer.displaySymbexSD(*executedEngine,
				getResultExecutionGraph(),
				showAssign, showTransition, enabledNumerization);
	}

	return errorMessageSD("NO DISPLAY: INVALID EXECUTED ENGINE !");
}

std::string Py_Result::displayUserText(bool showAssign,
		bool showTransition, bool enabledNumerization) const
{
	if( executedEngine != nullptr )
	{
		Py_Display displayer;

		return displayer.displaySymbexUserText(*executedEngine,
				getResultExecutionGraph(),
				showAssign, showTransition, enabledNumerization);
	}

	return "NO USER TEXT: INVALID EXECUTED ENGINE !";
}


std::string Py_Result::report() const
{
	if( executedEngine != nullptr )
	{
		StringOutStream outStr;
		executedEngine->report(outStr);

		return outStr.str();
	}

	return "NO REPORT: INVALID EXECUTED ENGINE !";
}
