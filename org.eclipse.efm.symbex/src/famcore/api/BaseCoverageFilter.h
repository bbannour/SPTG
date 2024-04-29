/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASECOVERAGEFILTER_H_
#define BASECOVERAGEFILTER_H_

#include  <famcore/api/AbstractProcessorUnit.h>

#include <collection/Typedef.h>
#include <famcore/api/AvmCoverageHeuristicProperty.h>
#include <famcore/api/AvmCoverageStatistics.h>
#include <famcore/StatemachineReachability.h>


namespace sep
{


class BaseCoverageFilter :
		public AbstractProcessorUnit,
		public IHeuristicContextWeight
{

protected:
	/**
	 * ATTRIBUTE
	 */
	bool mMinimizationFlag;
	bool mNormalizationFlag;

	std::size_t mBackwardAnalysisLookaheadDepth;
	std::size_t mForwardAnalysisLookaheadDepth;

	StatemachineReachability mStatemachineReachability;

	AvmCoverageHeuristicProperty mHeuristicProperty;

	AvmCoverageStatistics mCoverageStatistics;

	ListOfExecutionContext mListOfLeafEC;
	ListOfExecutionContext mListOfPositiveEC;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseCoverageFilter(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			avm_computing_process_stage_t requiredStage,
			const std::uint8_t * aPrecedence/* = DEFAULT_PRECEDENCE_OF_PROCESSOR*/)
	: AbstractProcessorUnit(aManager, wfParameterObject, requiredStage, aPrecedence),
	IHeuristicContextWeight( ),

	mMinimizationFlag( true ),
	mNormalizationFlag( true ),

	mBackwardAnalysisLookaheadDepth( AVM_NUMERIC_MAX_SIZE_T ),
	mForwardAnalysisLookaheadDepth ( AVM_NUMERIC_MAX_SIZE_T ),

	mStatemachineReachability( *this ),

	mHeuristicProperty( IHeuristicClass::HEURISTIC_BASIC_CLASS ),

	mCoverageStatistics( 100 , 0 ),

	mListOfLeafEC(),
	mListOfPositiveEC()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseCoverageFilter()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mMinimizationFlag
	 * mNormalizationFlag
	 */
	bool isMinimizationFlag()
	{
		return( mMinimizationFlag );
	}

	bool isNormalizationFlag()
	{
		return( mNormalizationFlag );
	}


	/**
	 * mCoverageStatistics
	 */
	inline AvmCoverageStatistics & getCoverageStatistics()
	{
		return mCoverageStatistics;
	}

	inline void resetCoverageStatistics()
	{
		return mCoverageStatistics.resetCoverageCounter();
	}


	/**
	 * CONFIGURE
	 */
	inline virtual std::string getDefaultSpiderTraceFormatter() const override
	{
		return( OSS() << " $coverage(%1% / %2%)" );
	}

	inline virtual std::string getDefaultEvalTraceFormatter() const override
	{
		return( OSS() << "  coverage< "
				<< getParameterWObject()->getFullyQualifiedNameID()
				<< " >: %1% / %2%" );
	}

	virtual bool configureImpl() override;


	/**
	 * PRE-FILTER
	 */
	virtual bool prefilter() override;


	/**
	 * PRE-PROCESS
	 */
	virtual bool preprocess() override;

	/**
	 * EXIT API
	 */
	virtual bool exitImpl() override
	{
		// SET EXIT CODE
		mCoverageStatistics.setExitCode();

		return true;
	}


	/**
	 * FILTERING FINALIZE
	 */
	virtual bool filteringFinalize() override;


	////////////////////////////////////////////////////////////////////////////
	// FINAL SLICING TOOLS
	////////////////////////////////////////////////////////////////////////////
	virtual bool isSliceableContext(ExecutionContext & anEC) const override;


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR REQUEST API
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GOAL_ACHIEVED
	 */
	virtual void handleRequestGoalAchieved() override;


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
	virtual void traceMinimumPreEval(
			OutStream & os, const ExecutionContext & anEC) const override;

	virtual void traceDefaultPreEval(
			OutStream & os, const ExecutionContext & anEC) const override;


	virtual void traceBoundEval(OutStream & os) const override;

	virtual void reportEval(OutStream & os) const override;

};



////////////////////////////////////////////////////////////////////////////////
// PROCESSOR UNIT AUTO REGISTRATION FACTORY
// for automatic registration in the processor repository
////////////////////////////////////////////////////////////////////////////////

template< class ProcessorT >
class AutoRegisteredCoverageProcessorUnit :  public  BaseCoverageFilter
{

public:
	/**
	 * TYPDEDEF
	 */
	typedef AutoRegisteredCoverageProcessorUnit< ProcessorT >
				RegisteredCoverageProcessorUnit;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AutoRegisteredCoverageProcessorUnit(SymbexControllerUnitManager & aManager,
			const WObject * wfParameterObject,
			avm_computing_process_stage_t requiredStage,
			const std::uint8_t * aPrecedence/* = DEFAULT_PRECEDENCE_OF_PROCESSOR*/)
	: BaseCoverageFilter(aManager, wfParameterObject, requiredStage, aPrecedence)
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AutoRegisteredCoverageProcessorUnit()
	{
		// Force Instanciate
		(void) & AUTO_REGISTER_TOOL;
	}


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 */
	static struct AutoRegisterProcessorFactory  :
			public ProcessorUnitRegistrationImpl< ProcessorT >
	{
		AutoRegisterProcessorFactory()
		: ProcessorUnitRegistrationImpl< ProcessorT >(
				ProcessorT::QNID() , ProcessorT::QNID1() ,
				ProcessorT::QNID2(), ProcessorT::QNID3() )
		{
			//!! NOTHING
		}

	}  AUTO_REGISTER_TOOL;
	// end registration


	/**
	 * API
	 */
	inline const IProcessorUnitRegistration & REGISTER_TOOL() const override
	{
		return( AUTO_REGISTER_TOOL );
	}

	inline bool isRegisterTool(
			const IProcessorUnitRegistration & aRegisterTool) const
	{
		return( AUTO_REGISTER_TOOL.isEquals( aRegisterTool ) );
	}

};


template< class ProcessorT > typename
AutoRegisteredCoverageProcessorUnit< ProcessorT >::AutoRegisterProcessorFactory
AutoRegisteredCoverageProcessorUnit< ProcessorT >::AUTO_REGISTER_TOOL;


}

#endif /* BASECOVERAGEFILTER_H_ */
