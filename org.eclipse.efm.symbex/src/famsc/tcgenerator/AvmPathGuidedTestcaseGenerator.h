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

#ifndef AVM_PATH_GUIDED_TESTCASE_GENERATOR_H_
#define AVM_PATH_GUIDED_TESTCASE_GENERATOR_H_

#include <famcore/api/BaseCoverageFilter.h>

#include "AvmQuiescenceFactory.h"
#include "AvmTraceDeterminismFactory.h"
#include "AvmTestCaseStatistics.h"

#include <fml/executable/ExecutableForm.h>

#include <fml/trace/TraceChecker.h>
#include <fml/trace/TraceFilter.h>


namespace sep
{

class ExecutionContext;
class SymbexControllerUnitManager;


class AvmPathGuidedTestcaseGenerator  :
		public AutoRegisteredCoverageProcessorUnit< AvmPathGuidedTestcaseGenerator >
{

	AVM_DECLARE_CLONABLE_CLASS( AvmPathGuidedTestcaseGenerator )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"controlled#width#eval",
			CONS_WID3("controlled", "width", "eval") )
	// end registration

public:
	/**
	 * ATTRIBUTE
	 */
	AvmQuiescenceFactory mQuiescenceFactory;

	AvmTraceDeterminismFactory mTraceDeterministismFactory;

	AvmTestCaseStatistics mTestCaseStatistics;

	SolverDef::SOLVER_KIND mSolverKind;

	ExecutableForm mLocalExecutableForm;

	TraceChecker mTraceChecker;

	AvmCode mTraceTestPurpose;
	AvmCode mTraceCommunicationIO;

	AvmCode mUncontrollable;
	TraceFilter mUncontrollableTraceFilter;

	// Computing Local Variables
	std::size_t mTraceOffset;

	ExecutionContext::ListOfPtr mCurrentTestPurposeEC;
	ExecutionContext::ListOfPtr mSatTestPurposeEC;

	bool mGoalAchieved;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmPathGuidedTestcaseGenerator(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmPathGuidedTestcaseGenerator()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 * mUncontrollableTraceFilter
	 */
	const TraceFilter & getUncontrollableTraceFilter() const
	{
		return mUncontrollableTraceFilter;
	}

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl() override;


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void reportMinimum(OutStream & os) const override;

	virtual void reportDefault(OutStream & os) const override;

	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

//	virtual bool preprocess() override;
//
//	virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize() override;

	virtual bool prefilter() override;

	virtual bool prefilter(ExecutionContext & anEC) override;

	virtual bool filteringFinalize() override;

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

    virtual bool postprocess() override;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void toStream(OutStream & os) const override
	{
		if( mParameterWObject != nullptr )
		{
			mParameterWObject->toStream(os);
		}
	}

};


} /* namespace sep */

#endif /* AVM_PATH_GUIDED_TESTCASE_GENERATOR_H_ */
