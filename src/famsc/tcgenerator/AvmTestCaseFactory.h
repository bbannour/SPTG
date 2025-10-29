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

#ifndef AVM_TESTCASE_FACTORY_H_
#define AVM_TESTCASE_FACTORY_H_

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/infrastructure/System.h>
#include <fml/infrastructure/Port.h>
#include <fml/infrastructure/Variable.h>

#include <fml/runtime/ExecutionContext.h>

#include <map>

namespace sep
{

class AvmOutputNormalizer;
class AvmPathGuidedTestcaseGenerator;
class AvmTestCaseStatistics;
class BaseTypeSpecifier;
class BFList;
class EvaluationEnvironment;
class InteractionPart;
class Machine;
class PropertyPart;
class Symbol;
class TraceFilter;

class AvmTestCaseFactory
{

public:
	/**
	 * ATTRIBUTE
	 */
	AvmPathGuidedTestcaseGenerator & mProcessor;
	EvaluationEnvironment & ENV;

	const Symbol & mQuiescencePortTP;

	const TraceFilter & mUncontrollableTraceFilter;

	AvmTestCaseStatistics & mTestCaseStatistics;

	ExecutionContext::VectorOfConstPtr mTestPurposeTrace;
	InstanceOfData::Table mTestPurposeInoutParams;
	InstanceOfData::Table mTestPurposeClockParams;
	ExecutionData mVarTC_subst_mParamTP_ED;
	BF mTestPurposePathCondition;
	System & mSystemSUT;
	System mSystemTC;
	Machine * mMachineTC;
	Port::Table mOutputPortSUT_toInputTC;
	Port::Table mUncontrollableSUT_toInputTC;
	BF mQuiescencePortTC;
	BF mVariable_TC_TM;
	BF mVariable_TC_Clock;
	Variable::Table mNewfreshInitialVars;
	Variable::Table mNewfreshTraceVarsTP;
	Variable::Table mNewfreshInitialTraceVarsTP;
	Machine * mStateTC_PASS;
	Machine * mStateTC_FAIL_OUT;
	Machine * mStateTC_FAIL_DUR;
	Machine * mStateTC_INC_OUT;
	Machine * mStateTC_INC_DUR;
	Machine * mStateTC_INC_UC_IN_SPEC;
	Machine * mStateTC_INC_UC_IN_USPEC;
	std::map<std::uint32_t, BF> mExecutionContextIdGuardMap;
	AvmOutputNormalizer & mOutputNormalizer;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTestCaseFactory(AvmPathGuidedTestcaseGenerator & aProcessor,
			AvmOutputNormalizer & outputNormalizer,
			AvmTestCaseStatistics & aTestCaseStatistics,
			const Symbol & aQuiescencePortTP);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTestCaseFactory()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// TEST CASE BUILDER
	////////////////////////////////////////////////////////////////////////////

	void buildTestCase();

	void buildStructure(const System & sutSystem, System & tcSystem);

	void addPorts(PropertyPart & tcPropertyPart,
			InteractionPart * tcInteractionPart, const PropertyPart & sutPropertyPart);

	void addVariables(PropertyPart & tcPropertyDecl,
			InstanceOfData::Table & tpInoutParameters,
			InstanceOfData::Table & tpClockParameters);

	void addType(const Variable::Table & portParameters);
	void addType(const BaseTypeSpecifier & paramType);
	void addType(const DataType & paramType);

	bool buildStatemachineTC();

	Machine * buildStep(Machine & tcSourceState,
			const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);

	Machine * buildStepSimplified(Machine & tcSourceState,
			const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);


	void saveTestCaseJson(const System & aSystemTC);
	void saveTestCaseSmtJson(const System & aSystemTC);

	void saveGenericTestCaseJson(OutStream & out, const System & aSystemTC,
			const auto & strVarTypeFunct, const auto & strFormulaFunc);


	////////////////////////////////////////////////////////////////////////////
	// RULES FOR TESCASE GENERATION
	////////////////////////////////////////////////////////////////////////////
	BFCode boundTimeOutCondition(const ExecutionContext & tcSourceEC);
	BFCode boundTimeOutCondition_Simplified(const ExecutionContext & tcSourceEC);
	BFCode boundTimeOutCondition_Simplified(
			const ExecutionContext & tcSourceEC, const BF & guardCondition);

	BF targetPathCondition(const ExecutionContext & tcTargetEC);

	BFCode unboundTimeOutCondition(const ExecutionContext & tcSourceEC);
	BFCode unboundTimeOutCondition_Simplified(const ExecutionContext & tcSourceEC);

	BF simplifyGuardCondition(const ExecutionContext & tcSourceEC,
			const Machine & tcSourceState, const BF & guardCondition);

	// Utils for simplified version
	BF getPathCondition_Simplified(const ExecutionContext & anEC, bool & isnotfound);

	void  mapExecutionContextGuard_Simplified(const ExecutionContext & anEC, const BF & aGuard);

//	BF boundTimeOutCondition_Simplified(const ExecutionContext & tcSourceEC);
//	BF unboundTimeOutCondition_Simplified(const ExecutionContext & tcSourceEC);

	BF targetPathCondition_Simplified(const ExecutionContext & tcTargetEC);


	// PROGRESS
	Machine * applyRule_R01_Progress_Stimulation(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	Machine * applyRule_R01_Progress_Stimulation_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	Machine * applyRule_R02_Progress_SpecifiedOutput(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	Machine * applyRule_R02_Progress_SpecifiedOutput_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	Machine * applyRule_R03_Progress_UncontrollableInput_Specified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	Machine * applyRule_R03_Progress_UncontrollableInput_Specified_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	// PASS
	Machine * applyRule_R04_Pass_SpecifiedOutput(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	Machine * applyRule_R04_Pass_SpecifiedOutput_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	Machine * applyRule_R05_Pass_SpecifiedQuiescence(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	Machine * applyRule_R05_Pass_SpecifiedQuiescence_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	// INCONCLUSIVE
	void applyRule_R06_Inconclusive_SpecifiedOutput(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	void applyRule_R06_Inconclusive_SpecifiedOutput_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	void applyRule_R07_Inconclusive_UncontrollableInput_Specified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	void applyRule_R07_Inconclusive_UncontrollableInput_Specified_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	void applyRule_R08_Inconclusive_UncontrollableInput_unspecified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const BF & ucInPort, const ExecutionContext & tcTargetEC);

	void applyRule_R08_Inconclusive_UncontrollableInput_unspecified_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const BF & ucInPort, const ExecutionContext & tcTargetEC);


	void applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);

	BF compute_R09_QuiescenceCondition(const ExecutionContext & tcSourceEC);

	void applyRule_R09_Inconclusive_SpecifiedQuiescence_Admissible_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);

	BF compute_R09_QuiescenceCondition_Simplified(
			const ExecutionContext & tcSourceEC, const Machine & tcSourceState);

	// FAIL
	void applyRule_R10a_Fail_UnspecifiedOutput(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);

	void applyRule_R10a_Fail_UnspecifiedOutput_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
		const BFCode & comTrace, const ExecutionContext & tcTargetEC);


	void applyRule_R10b_Fail_UnspecifiedOutput(Machine & tcSourceState,
			const ExecutionContext & tcSourceEC, const BF & obsPort,
			const ExecutionContext & tcTargetEC);

	void applyRule_R10b_Fail_UnspecifiedOutput_Simplified(Machine & tcSourceState,
			const ExecutionContext & tcSourceEC, const BF & obsPort,
			const ExecutionContext & tcTargetEC);


	void applyRule_R11_Fail_UnspecifiedQuiescence(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);

	BF compute_R11_QuiescenceCondition(
			const ExecutionContext & tcSourceEC, const Machine & tcSourceState);

	void applyRule_R11_Fail_UnspecifiedQuiescence_Simplified(
			Machine & tcSourceState, const ExecutionContext & tcSourceEC,
			const ExecutionContext & tcTargetEC);

	BF compute_R11_QuiescenceCondition_Simplified(const ExecutionContext & tcSourceEC);


};


} /* namespace sep */

#endif /* AVM_TESTCASE_FACTORY_H_ */
