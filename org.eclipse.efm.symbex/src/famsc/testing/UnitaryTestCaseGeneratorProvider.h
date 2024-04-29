/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 Sep. 2017
 *
 * Contributors:
 *  Ngo Minh Thang Nguyen (CEA LIST) ngo-minh-thang.nguyen@cea.fr
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FAM_TESTING_UNITARYTESTCASEGENERATORPROVIDER_H_
#define FAM_TESTING_UNITARYTESTCASEGENERATORPROVIDER_H_

#include <famsc/testing/AbstractTestCaseGeneratorProvider.h>
#include <famsc/testing/TestCaseHelper.h>

#include <fml/expression/AvmCode.h>
#include <fml/workflow/WObject.h>

#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>
#include <fml/trace/TracePoint.h>
#include <fml/symbol/TableOfSymbol.h>


#include <algorithm>
#include <map>

namespace sep{

class ExecutionContext;
class InstanceOfPort;
class OutStream;


class UnitaryTestCaseGeneratorProvider :
		public AbstractTestCaseGeneratorProvider,
		public TestCaseHelper
{

protected:
	/**
	 * ATTRIBUTE
	 */

	//the controllable signals to compute correctly verdicts inconc/fail
	AvmCode mTPasTransitionSequence;

	AvmCode mQUIESCENCE;

	avm_offset_t mCurrentTraceIndex;

	TraceChecker mTraceChecker;

	//the controllable signals to compute correctly verdicts inconc/fail
//	TraceFilter mProjection;

	TableOfSymbol mTableOfPort;

	ListOfExecutionContext mListOfECToErase;

	ListOfExecutionContext mListOfECWithOutputForTestCase;

	// Test case graph
	ExecutionContext * mRootGraphTestCaseEC;
	ExecutionContext * mTestCaseEC;
	ExecutionContext * mTestCaseChildEC;
	std::map< ExecutionContext * , ExecutionContext * > mMapOfECToItsClone;
	ExecutionContext * mRootTP;
	Symbol mPortQuiencenceData;
	Symbol mPortQuiencenceTime;

	RuntimeID mQuiescenceRID;
	RuntimeID mFailRID;
	RuntimeID mINCONCRID;

	System * mTestcaseSystem;

	Machine * mStateMachine;

	ListOfExecutionContext mListOfECToAddInProjection;

	ListOfExecutionContext mListECToDelete;

	ListOfExecutionContext mListECUpdated;

	Vector< std::pair<ExecutionContext *, Machine * > > mVectorOfECAndState;

	//	Vector< std::pair<Machine *, BFList > > mVectorOfStateAndBSen;

	std::map< Machine *, BFList > mMapOfStateAndBSen;

	std::map< Machine *, BFList > mMapOfStateAndDataVarsInst;

	Vector< std::pair<Port *, InstanceOfPort *  > > mVectorOfPortAndRID;

	Vector< Connector *  > mListOfConnector;

	Vector< BF > mListOfEnum;

	List<Variable *> mListVariablesTestCase;

	ListOfExecutionContext mListECWithFlags;

	unsigned int mIndexState;

	Connector * mConnector;

	InteractionPart * mInteractionPart;

	BFList mListOfDelaysPtCTestPurpose;

	ListOfConstExecutionContext mListECsToResetClock;

	clock_t mTStart;

	BF mClockTestCase;

	BF mBoundB;

	ListOfExecutionContext mListOfTreatedECs;

	std::string mINITIALSTATE;

	std::string mPASSSTATE;

	std::string mINCONCSTATE;

	std::string mFAILSTATE;

	Vector< std::pair < std::string, BFList> > mVectorOfPathConditions;

public:
	/**
	 * CONSTRUCTOR
	 */
	UnitaryTestCaseGeneratorProvider(TestCaseGenerator & aTestCaseGenerator);

	~UnitaryTestCaseGeneratorProvider()
	{

	}

	/**
	 * CONFIGURE allows to take into account user's parameters: at the moment,
	 * it takes as input ... à compléter
	 */
	virtual bool configureImpl(const WObject * wfParameterObject) override;

	/**
	 * REPORT TRACE
	 */
//	virtual void reportDefault(OutStream & os) const override;

	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preProcessing
	 */
	virtual bool preprocess() override;

	/**
	 * postprocessing
	 */
	virtual bool postprocessImpl() override;

	void addECToListECWithFlags(const ExecutionContext & rootEC);

	void deleteUnobservableDelays( ExecutionContext & anEC );

	void specifyQuiescence(ExecutionContext & aProjectedGraph );

	void generateTestCases(ExecutionContext & rootEC,
			const BF & pathConditionTestPurpose,
			const BF & pathTimedConditionTestPurpose,
			std::string nameMachine );

	void createTransitionsInTestCase(ExecutionContext & anEC,
			Machine * inconcState, Machine * failState,
			Machine * passState, const BF & pathConditionTestPurpose,
			const BF & pathTimedConditionTestPurpose,
			const BF & clockTestCase );

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * filteringInitialize
	 */
//	virtual bool filteringInitialize() override;

	/**
	 * preFiltering
	 */
	virtual bool prefilter(ExecutionContext & anEC) override;

	/**
	 * postFiltering
	 * Every post filter has to implement this method
	 */
//	virtual bool postfilter() override;
//
//	virtual bool postfilter(ExecutionContext & anEC) override;

	/**
	 * UTILS
	 */
	void getAllExecutionContextsForResetClocks(
			const BF & pathTimedConditionTestPurpose);


//	void createFailDueToTimeInGraph( ExecutionContext * parentEC,
//			ListOfExecutionContext & listofECToAdd);
//
//	void createFailDueToDataInGraph( ExecutionContext * parentEC,
//			ListOfExecutionContext & listofECToAdd);


	void createInconcInGraph(ExecutionContext * childEC,
			ExecutionContext * parentEC, ListOfExecutionContext & listofECToAdd);

	Port * createNewPort( ExecutionContext * anEC,
			AvmCode::OperandCollectionT newfreshList,
			InstanceOfPort * anInstanceOfPort,
			RuntimeID & portCompRID );

	Port * createNewPortForRemainingInstanceOfPort(
			ArrayOfBF & listOfParams,
			InstanceOfPort * anInstanceOfPort );

	void createNewComRoute( ExecutionContext * anEC,
			InstanceOfPort * anInstanceOfPort,
			Port * aPort,
			RuntimeID & portCompRID );

	void createNewComRouteForRemainingInstanceOfPort(
			InstanceOfPort * anInstanceOfPort,
			Port * aPort );

	BF createNewTypesEnum(AvmCode::OperandCollectionT newFreshList);

	void createBoundBForTestCase();

	void createClockForTestCase( BF delay );

	void createCoveredInTestCase(ExecutionContext * childEC,
			Machine * newState,	Transition * newTran, Machine * parentState,
			Machine * failState, Machine * inconcState,
			BF pathConditionTestPurpose, const BF & clockTestCase,
			BFList OCond, BFList listInstDataVars,
			ListOfExecutionContext listECForInconc );

	void createFailRemainingPortsInTestCase( InstanceOfPort * aRemainingPort,
			ExecutionContext * parentEC, Transition * newTran,
			Machine * parentState, Machine * failState,
			const BF & clockTestCase, BFList listInstDataVars );

	void createInconcRemainingInputPortsInTestCase( InstanceOfPort * aRemainingPort,
			ExecutionContext * parentEC, Transition * newTran,
			Machine * parentState, Machine * inconcState,
			const BF & clockTestCase, BFList listInstDataVars );

	void createFailForSpecifiedTransition(BF formulaPhiTilde,
			AvmCode::OperandCollectionT varsOfPort,	BFCode codeResettingClock,
			BFCode action, Transition * tranFail, Machine * parentState,
			Machine * failState, const BF & clockTestCase, BF delay,
			RoutingData aRoutingData );

	void createFailForTimeInTestCase(ExecutionContext * childEC,
			Machine * newState, Transition * newTran, Machine * parentState,
			Machine * failState, const BF & clockTestCase,
			BFList bSenForNewTran, BFList listInstVars );

	void createInconcInTestCase(ExecutionContext * childEC,
			Transition * tranItm, Machine * parentState,
			Machine * failState, Machine * inconcState,
			const BF & clockTestCase, BFList OCond,
			BFList listInstDataVars, ListOfExecutionContext listECForInconc,
			BF pathConditionTestPurpose);

	void createInconcInputForSamePortInTestCase(ExecutionContext * childEC,
			Machine * inconcState, Machine * failState, BFList bSenForNewTran,
			BFList listInstVars, AvmCode::OperandCollectionT newFreshList,
			BF & pathConditionInconcs, BF & pathTimeConditionInconcs );

	void createInconcUnderSpecifiedInTestCase(BF formulaPhiTilde,
			AvmCode::OperandCollectionT varsOfPort, BFCode codeResettingClock,
			BFCode action, Transition * aTran, Machine * parentState,
			Machine * inconcState, const BF & clockTestCase,
			RoutingData aRoutingData);

	void createInconcOutputForSamePortInTestCase(ExecutionContext * childEC,
			Machine * itmState,	Machine * inconcState, Machine * failState,
			BFList bSenForNewTran, BFList listInstVars,
			AvmCode::OperandCollectionT newFreshList,
			BF & pathConditionInconcs, BF & pathTimeConditionInconcs );

	void createNewTimeVariables(BF delay);

	void createNewVariables(AvmCode::OperandCollectionT newfreshList);

	void createPassInGraph(ExecutionContext * childEC,
			ExecutionContext * parentEC,
			ListOfExecutionContext & listofECToAdd);

	void createPassInTestCase(ExecutionContext * childEC,
			Transition * newTran, Machine * parentState,
			Machine * passState, Machine * failState, Machine * inconcState,
			const BF & clockTestCase, BFList OCond,	BFList listInstDataVars,
			ListOfExecutionContext listECForInconc,
			BF pathConditionTestPurpose);

	void createQuiescenceInTestCase(ExecutionContext * childEC,
			Transition * tranItm, Machine * parentState,
			Machine * inconcState, Machine * failState,
			const BF & clockTestCase, BFList bSenForNewTran,
			BFList listInstVars );

//	void createInconcTransitionForSamePortForTimeInTestCase(
//	ExecutionContext * childEC, Machine * itmState,	Machine * inconcState );

//	void createFailTransitionForTimeInTestCaseBis(ExecutionContext * childEC,
//	Machine * itmState, Machine * failState );

	void addQuiescenceDuetoDataInSpec(ExecutionContext * childEC,
			BF guardsDataOutputTransitions, ExecutionContext * parentEC);

	void addQuiescenceDuetoTimeInSpec(ExecutionContext * childEC,
			BF guardsTimeOutputTransitions, ExecutionContext * parentEC);

//	void createFailRemainingPortsInGraph(ExecutionContext * childEC,
//			ExecutionContext * parentEC,
//			InstanceOfPort * aPort, ListOfExecutionContext & listofECToAdd );

// TODO DELETE
//	void createListOfPortWithNodeConditions(InstanceOfPort * aPort,
//	ExecutionContext * childEC);


};

}

#endif /* FAM_TESTING_UNITARYTESTCASEGENERATORPROVIDER_H_ */
