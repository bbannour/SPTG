/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_LABELLED_TESTCASE_FACTORY_H_
#define AVM_LABELLED_TESTCASE_FACTORY_H_

#include <common/BF.h>

#include <fml/infrastructure/System.h>

#include <fml/runtime/ExecutionContext.h>

namespace sep
{

class AvmPathGuidedTestcaseGenerator;
class BFList;
class Machine;
class Port;
class PropertyPart;
class Variable;

class AvmLabelledTestCaseFactory
{

public:
	/**
	 * ATTRIBUTE
	 */
	AvmPathGuidedTestcaseGenerator & mProcessor;

	const Symbol & mQuiescencePortTP;

	ExecutionContext::ListOfConstPtr testPurposeTrace;

	System & sutSystem;
	System tcSystem;
	Machine * tcMachine;
	BF tcQuiescencePort;
//	Machine * tcStateFAIL;
//	Machine * tcStateINC;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmLabelledTestCaseFactory(
			AvmPathGuidedTestcaseGenerator & aProcessor, const Symbol & aQuiescencePortTP);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmLabelledTestCaseFactory()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// TEST CASE BUILDER
	////////////////////////////////////////////////////////////////////////////

	void buildTestCase();

	void buildStructure(const System & sutSystem, System & tcSystem);

	void addPorts(PropertyPart & tcPropertyPart,
			const PropertyPart & sutPropertyPart);


	bool buildStatemachine();

	Machine * buildState(Machine & tcSourceState,
			const ExecutionContext & tcSourceEC, const ExecutionContext & tcTargetEC);


	void sutUnexpectedOutput(const ExecutionContext & anEC,
			const BF tpOutputPort, BFList & specSutOutputPort);


	void addIncInputTransition(const ExecutionContext & anEC, Machine & tcSourceState,
			const BFList & specSutOutputPort, bool groupIncInput);

	void createIncInputTransition(const ExecutionContext & anEC, Machine & tcSourceState,
			const BFCodeList & allIncInputStatement, bool groupFailedInput);


	void addFailQuiescenceTransition(
			const ExecutionContext & anEC,Machine & tcSourceState);


	void addFailInputTransition(const ExecutionContext & anEC,
			Machine & tcSourceState, bool groupFailedInput);

	void addFailInputTransition(const ExecutionContext & anEC, Machine & tcSourceState,
			const BFList & specSutOutputPort, bool groupFailedInput);

	void createFailInputTransition(const ExecutionContext & anEC, Machine & tcSourceState,
			const BFCodeList & allFailedInputStatement, bool groupFailedInput);

};


} /* namespace sep */

#endif /* AVM_LABELLED_TESTCASE_FACTORY_H_ */
