/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 28 nov. 2011
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_TESTING_TESTCASEGENERATIONHELPER_H_
#define FAM_TESTING_TESTCASEGENERATIONHELPER_H_

#include <common/AvmPointer.h>
#include <famcore/api/AbstractProcessorUnit.h>

#include <fml/expression/AvmCode.h>
#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/symbol/TableOfSymbol.h>
#include <fml/workflow/WObject.h>

#include <sew/Workflow.h>

#include <algorithm>
#include <map>

namespace sep{

class ExecutionContext;
class InstanceOfPort;
class OutStream;


class TestCaseGenerationHelper
{

protected:

public:
	/**
	 * CONSTRUCTOR
	 */
	TestCaseGenerationHelper()
	{
			//!! NOTHING
	}

	~TestCaseGenerationHelper()
	{
		//!! NOTHING
	}


	/**
	 * UTILS
	 */
	InstanceOfPort * getIOPort(const BF & ioTrace);

//    InstanceOfPort * getIOPort(const BF & ioTrace, BFList & paramsList);

	const RuntimeID & getIORuntimeID(const BF & ioTrace);

	InstanceOfPort * getIOPort(const BF & ioTrace, RuntimeID & aRID);

	void keepDelayOfTransition(const BF & ioTrace, BFList & newFreshTrace);

	BF getDelayOfTransition(const BF & ioTrace);

	BFList getParamsListOfPort(const BF & ioTrace);

	AvmCode::OperandCollectionT getTermListOfPort(const BF & ioTrace);

	void getDataVarsNonInstantiatedInGuard(const BF & pathConditionTestPurpose,
			AvmCode::OperandCollectionT & listOfVarsNonInstantiated);

	void getTimeVarsNonInstantiatedInGuard(const BF & pathTimedConditionTestPurpose,
			AvmCode::OperandCollectionT & listOfVarsNonInstantiated);

	BFList getBSenInQuestion(const BFList & BSen, AvmCode::OperandCollectionT & listOfVarsNonInstantiated);

	void setIOMirroring(ExecutionContext & anEC);

	BF getIOMirroring(const BF & ioTrace);



//	const BF & getIOPortParameter(ExecutionContext & anEC);
//
//	const BF & getIOPortParameter(const BF & ioTrace);
//
//
//	const void getIOPortParameter(InstanceOfPort * aPort, ExecutionContext & anEC, BFList & paramsList);
//
//	const void getIOPortParameter(InstanceOfPort * aPort, const BF & ioTrace, BFList & paramsList);


	void verifyTreatedPortForFail(Vector<InstanceOfPort *> & listOfPorts, InstanceOfPort * aPort);

	void getListOfOutputPorts(InstanceOfPort * aPort, Vector<InstanceOfPort *> & listOfPorts);

	BF createNotEqualityOnFreshVars(ExecutionContext * parentEC, RuntimeID portCompRID,
			AvmCode::OperandCollectionT newfreshList, InstanceOfPort * aPort );

	BF createEqualityOnFreshVarsForGraph(ExecutionContext * parentEC,
			AvmCode::OperandCollectionT newfreshList );

	BF createEqualityOnFreshVars(ExecutionContext * parentEC,
			AvmCode::OperandCollectionT newfreshList, BFList & listInstDataVars );


	void createInconcInGraph(ExecutionContext * childEC,
			ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd);

	BFCode resettingClockTestCase( Variable * clockTestCase );

	BFCode readingValueOfClockTestCase(Variable * clockTestCase, BF delay);


	void addRunnableTrace(ExecutionContext * childEC, const RuntimeID & compRID);

//	void createFailForQuiescenceInTestCase(ExecutionContext * childEC,
//			ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd);

	void createQuiescenceInGraph(ExecutionContext * childEC,
			ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd);

	void verifyIncontrollablePath(ExecutionContext * childEC);

	// TODO DELETE
	//void createListOfPortWithNodeConditions(InstanceOfPort * aPort, ExecutionContext * childEC);


};

}

#endif /* FAM_TESTING_TESTCASEGENERATIONHELPER_H_ */
