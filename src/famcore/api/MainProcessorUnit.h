/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef MAINPROCESSORUNIT_H_
#define MAINPROCESSORUNIT_H_

#include  <famcore/api/AbstractProcessorUnit.h>
#include  <famcore/debug/IDebugProcessorProvider.h>

#include <common/BF.h>

#include <fml/builtin/Identifier.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/expression/AvmCode.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/trace/TraceChecker.h>

#include <sew/Configuration.h>


namespace sep
{


class MainProcessorUnit final :
//		public AvmCloneableClass< MainProcessorUnit >,
		public AutoRegisteredProcessorUnit< MainProcessorUnit >,
		public IDebugProcessorProvider
{

	AVM_DECLARE_CLONABLE_CLASS( MainProcessorUnit )


	/**
	 * MAIN PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_3(
			"supervisor",
			"avm::processor.MAIN",
			"avm::core.filter.STOP_CRITERIA" )
	// end registration


public:
	/**
	 * ATTRIBUTE
	 */
	std::size_t mNodeCountLimit;

	std::size_t mSymbexEvalCountLimit;
	std::size_t mSymbexStepCountLimit;

	std::size_t mNodeHeightLimit;
	std::size_t mNodeWidthLimit;

	std::size_t mReportFrequency;
	std::size_t mReportPoint;

	std::size_t mSaveFrequency;
	std::size_t mSavePoint;

	std::size_t mStopCount;

	std::size_t mDeadlockCount;
	std::size_t mLivelockCount;

	std::size_t mStatementExitCount;

	std::size_t mStatementFatalErrorCount;
	std::size_t mSymbolicExecutionLimitationCount;

	std::size_t mMaxReachHeight;
	std::size_t mMaxReachWidth;

protected:

	std::string mInconditionalStopMarkerLocation;
	std::size_t mInconditionalStopMarkerCheckingPeriod;

	bool mInconditionalStopMarkerFlag;

	// Execution extension trace filter
	ExecutableForm mLocalExecutableForm;

	AvmCode mTraceObjective;

	TraceChecker mTraceChecker;

	// INFO ID
	BF mExitInfoID;
	BF mExitAllInfoID;
	BF mReturnInfoID;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	ExecutionContext * ptrEC;

	ListOfExecutionContext mAnteWaitingQueue;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	MainProcessorUnit(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject = nullptr);

	/**
	 * DESTRUCTOR
	 */
	virtual ~MainProcessorUnit()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mMaxReachHeight
	 * mMaxReachWidth
	 */
	inline std::size_t getMaxReachHeight() const
	{
		return mMaxReachHeight;
	}

	inline std::size_t getMaxReachWidth() const
	{
		return mMaxReachWidth;
	}


	/**
	 * Return true if the EC is re-executable
	 * And clean the structural stop criteria info
	 * like EVAL, NODE, HEIGHT, WIDTH, ABSOLUTE_STOP_MARKER
	 */
	inline static bool cleanFlagsIfReexecutable(ExecutionContext & anEC)
	{
		if( anEC.getFlags().isReexecutable() )
		{
			anEC.getwFlags().setReexecutable();

			return( true );
		}

		return( false );
	}


	/**
	 * CONFIGURE
	 */
	// SPIDER TRACE
	inline virtual std::string getDefaultSpiderInitTraceFormatter() const override
	{
		return( "\n<$spider(%1%:%2%:%3%:%4%)%5%\n" );
	}

	inline virtual std::string getDefaultSpiderStepTraceFormatter() const override
	{
		return( "\n$spider(%1%:%2%:%3%:%4%)%5%\n" );
	}

	inline virtual std::string getDefaultSpiderStopTraceFormatter() const override
	{
		return( "\n>$spider(%1%:%2%:%3%:%4%)%5%\n" );
	}


	// EVAL TRACE
	inline virtual std::string getDefaultEvalTraceFormatter() const override
	{
		return( "\nstep:%1% , context:%2% , height:%3% , width:%4%" );
	}

	inline virtual std::string getDefaultReportEvalTraceFormatter() const override
	{
		return( "\nstop:%1% , context:%2% , height:%3% , width:%4%" );
	}


	virtual bool configureImpl() override;


	/**
	 * REPORT TRACE
	 */

	virtual void reportSilent(OutStream & out) const override;

	virtual void reportMinimum(OutStream & out) const override;

	virtual void reportDefault(OutStream & out) const override;

	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & out) const override;


	/**
	 * SPIDER TRACE
	 */
	virtual void traceInitSpider(OutStream & os) const override;

	virtual void traceStepSpider(OutStream & os,
			const ExecutionContext & anEC) const override;

	virtual void traceStopSpider(OutStream & os) const override;

	/**
	 * EVAL TRACE
	 */
	virtual void traceMinimumPreEval(OutStream & os,
			const ExecutionContext & anEC) const override;

	virtual void traceDefaultPreEval(OutStream & os,
			const ExecutionContext & anEC) const override;


	virtual void traceMinimumPostEval(OutStream & os,
			const ExecutionContext & anEC) const override;

	virtual void traceDefaultPostEval(OutStream & os,
			const ExecutionContext & anEC) const override;


	virtual void traceBoundEval(OutStream & os) const override;

	virtual void reportEval(OutStream & os) const override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * POST PROCESS
	 */
	inline virtual bool preprocess() override
	{
		if( mTraceObjective.hasOperand() )
		{
			return( collectExtendedContext() );
		}

		return( true );
	}


	bool collectExtendedContext();

	void collectContext(
			ListOfExecutionContext & inputContext, ExecutionContext & anEC);

	void appendIfRequiredExtension(
			ListOfExecutionContext & inputContext, ExecutionContext & anEC);

	inline virtual bool postprocess() override
	{
		return( true );
	}

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preEval Filter
	 */
	virtual bool prefilter() override;
	virtual bool prefilter(ExecutionContext & anEC) override;

	bool finalizePrefiltering();


	/**
	 * postFilter
	 * Every post filter has to implement this method
	 */
	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;

	bool finalizePostfiltering();

	bool finalizePostfiltering(ExecutionContext & aChildEC);

	void setContextWidth(ExecutionContext & anEC);


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugEvalCommandImpl() override;

	void checkReadEvalStopScript();

};


}

#endif /*MAINPROCESSORUNIT_H_*/
