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

#include <fam/api/AbstractProcessorUnit.h>
#include <fam/debug/IDebugProcessorProvider.h>

#include <common/AvmPointer.h>
#include <common/BF.h>

#include <fml/builtin/Identifier.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/expression/AvmCode.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/trace/TraceChecker.h>

#include <sew/Configuration.h>


namespace sep
{


class MainProcessorUnit  :
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


protected:
	/**
	 * ATTRIBUTE
	 */
	avm_size_t mNodeCountLimit;
	avm_size_t mEvalStepLimit;
	avm_size_t mNodeHeightLimit;
	avm_size_t mNodeWidthLimit;

	avm_size_t mReportFrequency;
	avm_size_t mReportPoint;

	avm_size_t mSaveFrequency;
	avm_size_t mSavePoint;

	avm_size_t mStopCount;

	avm_size_t mDeadlockCount;
	avm_size_t mLivelockCount;

	avm_size_t mStatementExitCount;

	avm_size_t mStatementFatalErrorCount;
	avm_size_t mSymbolicExecutionLimitationCount;

	avm_size_t mMaxReachHeight;
	avm_size_t mMaxReachWidth;

	std::string mInconditionalStopMarkerLocation;
	avm_size_t mInconditionalStopMarkerCheckingPeriod;

	bool mInconditionalStopMarkerFlag;

	// Execution extension trace filter
	ExecutableForm mLocalExecutableForm;

	AvmCode mTraceObjective;

	TraceChecker mTraceChecker;

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	ExecutionContext * ptrEC;

	ListOfExecutionContext childEC;


public:

	MainProcessorUnit(SymbexControllerUnitManager & aManager,
			WObject * wfParameterObject = NULL)
	: RegisteredProcessorUnit(aManager,
			wfParameterObject, PRECEDENCE_OF_MAIN_PROCESSOR),
	IDebugProcessorProvider( this ),

	mNodeCountLimit ( AVM_NUMERIC_MAX_SIZE_T ),
	mEvalStepLimit  ( AVM_NUMERIC_MAX_SIZE_T ),
	mNodeHeightLimit( AVM_NUMERIC_MAX_SIZE_T ),
	mNodeWidthLimit ( AVM_NUMERIC_MAX_SIZE_T ),

	mReportFrequency( AVM_NUMERIC_MAX_SIZE_T ),
	mReportPoint( AVM_NUMERIC_MAX_SIZE_T ),

	mSaveFrequency( AVM_NUMERIC_MAX_SIZE_T ),
	mSavePoint( AVM_NUMERIC_MAX_SIZE_T ),

	mStopCount( 0 ),

	mDeadlockCount( 0 ),
	mLivelockCount( 0 ),

	mStatementExitCount( 0 ),

	mStatementFatalErrorCount( 0 ),
	mSymbolicExecutionLimitationCount( 0 ),

	mMaxReachHeight( 1 ),
	mMaxReachWidth( 1 ),

	mInconditionalStopMarkerLocation(),
	mInconditionalStopMarkerCheckingPeriod(AVM_NUMERIC_MAX_SIZE_T),

	mInconditionalStopMarkerFlag( false ),

	// Execution extension trace filter
	mLocalExecutableForm( getConfiguration().getExecutableSystem() , 0 ),
	mTraceObjective( OperatorManager::OPERATOR_OR ),
	mTraceChecker( ENV, &mLocalExecutableForm ),

////////////////////////////////////////////////////////////////////////////
	// for local used
	ptrEC( NULL ),
	childEC( )
	{
		//!! NOTHING
	}

	virtual ~MainProcessorUnit()
	{
		//!! NOTHING
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
	inline virtual std::string getDefaultPreEvalTraceFormatter() const
	{
		return( "\nstep:%1% , context:%2% , height:%3% , width:%4%" );
	}

	inline virtual std::string getDefaultPostEvalTraceFormatter() const
	{
		return( "\nstep:%1% , context:%2% , height:%3% , width:%4%" );
	}


	inline virtual std::string getDefaultBoundEvalTraceFormatter() const
	{
		return( "\nstep:%1% , context:%2% , height:%3% , width:%4%" );
	}

	inline virtual std::string getDefaultReportEvalTraceFormatter() const
	{
		return( "\nstop:%1% , context:%2% , height:%3% , width:%4%" );
	}


	bool configureImpl();


	/**
	 * REPORT TRACE
	 */

	virtual void reportSilent(OutStream & os) const;

	virtual void reportMinimum(OutStream & os) const;

	virtual void reportDefault(OutStream & os) const;

	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os);


	/**
	 * EVAL TRACE
	 */
	virtual void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const;

	virtual void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const;


	virtual void traceMinimumPostEval(
			OutStream & os, const ExecutionContext & anEC) const;

	virtual void traceDefaultPostEval(
			OutStream & os, const ExecutionContext & anEC) const;


	virtual void traceBoundEval(OutStream & os) const;

	virtual void reportEval(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PROCESSING API
	////////////////////////////////////////////////////////////////////////////
	/**
	 * POST PROCESS
	 */
	inline virtual bool preprocess()
	{
		if( mTraceObjective.nonempty() )
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

	inline virtual bool postprocess()
	{
		return( true );
	}

	////////////////////////////////////////////////////////////////////////////
	// FILTERING API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * preEval Filter
	 */
	virtual bool prefilter();
	virtual bool prefilter(ExecutionContext & anEC);

	bool finalizePrefiltering();


	/**
	 * postFilter
	 * Every post filter has to implement this method
	 */
	virtual bool postfilter();
	virtual bool postfilter(ExecutionContext & anEC);

	bool finalizePostfiltering();

	void setContextWidth(ExecutionContext * anEC);


	////////////////////////////////////////////////////////////////////////////
	// DEBUG PROCESSING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool debugEvalCommandImpl();

	void checkReadEvalStopScript();

};


}

#endif /*MAINPROCESSORUNIT_H_*/
