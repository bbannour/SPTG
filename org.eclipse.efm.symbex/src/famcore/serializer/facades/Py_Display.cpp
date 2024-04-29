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

#include "Py_Display.h"

#include  <famcore/serializer/CommonGraphicStatemachineSerializer.h>

#include  <famcore/serializer/GraphicStatemachineSerializer.h>
#include  <famcore/serializer/GraphVizExecutionGraphSerializer.h>
#include  <famcore/serializer/CommunicationGraphSerializer.h>

#include  <famcore/trace/AvmTraceGenerator.h>

#include <fml/infrastructure/System.h>

#include <fml/runtime/ExecutionContext.h>

#include <sew/facades/Py_Engine.h>


namespace sep
{

// Default display <=> displaySTS
std::string Py_Display::display(const System & aSystem,
		bool showStatement, bool showCommunication, bool showAssign)
{
	CommonGraphicStatemachineSerializer serializer;

	StringOutStream oss;

	serializer.format(oss, aSystem);

	return oss.str();
}


// Display Symbolic Transition System
std::string Py_Display::displaySTS(Py_Engine & engine, const System & aSystem,
		bool showStatement, bool showCommunication, bool showAssign)
{
	GraphicStatemachineSerializer serializer(
			engine.getControllerUnitManager(), WObject::_NULL_);

	StringOutStream oss;

	serializer.format(oss, aSystem);

	return oss.str();
}


// Display Symbolic Execution Graph
std::string Py_Display::displaySymbexGraph(
		Py_Engine & engine, const ExecutionContext & anEC,
		bool showTransition, bool showCommunication, bool showAssign)
{
	ListOfExecutionContext listofEC( const_cast< ExecutionContext * >(& anEC) );

	StringOutStream oss;

	GraphVizExecutionGraphSerializer::format(
			engine.getControllerUnitManager(), oss, listofEC,
			showTransition, showCommunication, showAssign);

	return oss.str();
}

// Display Symbolic Execution Trace as Sequence Diagram
std::string Py_Display::displaySymbexSD(
		Py_Engine & engine, const ExecutionContext & anEC,
		bool showAssign, bool showTransition, bool enabledNumerization)
{
	ListOfExecutionContext listofEC( const_cast< ExecutionContext * >(& anEC) );

	StringOutStream oss;

	AvmTraceGenerator::generateSequenceDiagram(
			engine.getControllerUnitManager(), oss, listofEC,
			showAssign, showTransition, enabledNumerization);

	return oss.str();
}

// Display Symbolic Execution Trace as User Textual Defined Format
std::string Py_Display::displaySymbexUserText(
		Py_Engine & engine, const ExecutionContext & anEC,
		bool showAssign, bool showTransition, bool enabledNumerization)
{
	ListOfExecutionContext listofEC( const_cast< ExecutionContext * >(& anEC) );

	StringOutStream oss;

	AvmTraceGenerator::generateUserTextualFormat(
			engine.getControllerUnitManager(), oss, listofEC,
			showAssign, showTransition, enabledNumerization);

	return oss.str();
}

std::string Py_Display::displayCommunicationGraph(const System& aSystem){
	CommunicationGraphSerializer serializer = CommunicationGraphSerializer();
	return serializer.format(aSystem);
}



} /* namespace sep */
