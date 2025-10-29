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

#ifndef AVMHITORJUMPPROCESSOR_H_
#define AVMHITORJUMPPROCESSOR_H_

#include <collection/Bitset.h>
#include <famcore/api/AvmCoverageStatistics.h>
#include <famcore/api/BaseCoverageFilter.h>

#include <fml/operator/OperatorLib.h>

#include <sew/SymbexControllerEventManager.h>


namespace sep
{

class BaseHitProcessor;
class ExecutionContext;
class SymbexControllerUnitManager;


class AvmHitOrJumpProcessor  :
		public AutoRegisteredCoverageProcessorUnit< AvmHitOrJumpProcessor > ,
		public IHandlerEventDestroyCtx
{

	AVM_DECLARE_CLONABLE_CLASS( AvmHitOrJumpProcessor )


	/**
	 * PROCESSOR FACTORY
	 * for automatic registration in the processor repository
	 * the [ [ FULLY ] QUALIFIED ] NAME ID
	 */
	AVM_INJECT_AUTO_REGISTER_QUALIFIED_ID_KEY_2(
			"coverage#behavior",
			"avm::processor.HIT_OR_JUMP" )
	// end registration


public:
	/**
	 * ATTRIBUTE
	 */
	BaseHitProcessor * mHitProcessor;

	bool mGlobalSearchScopeFlag;

	AVM_OPCODE mScheduler;

	bool mFoldingFlag;

	std::size_t mJumpDelta;
	std::size_t mJumpHeight;

	std::size_t mJumpTrialsCount;
	std::size_t mJumpTrialsLimit;

	bool mHitConsecutiveFlag;
	bool mHitMaxFlag;
	bool mHitLuckyFlag;
	bool mBacktrackFlag;

	std::size_t mHitCount;
	std::size_t mJumpCount;

	bool mHitFinalFlag;


	bool mJumpSliceFlag;

	AvmCoverageStatistics mFinalCoverageStatistics;

	bool mGoalAchieved;


	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	bool mAbsoluteStopContextFlag;

	bool mHitCaseFlag;

	std::size_t mSelectionCount;

	ListOfExecutionContext   mInitialRootEC;
	ListOfExecutionContext   mBufferLocalRootEC;

	ListOfExecutionContext   mRelativeRootEC;
	VectorOfExecutionContext mRelativeLeafEC;

	ListOfExecutionContext   mAbsoluteLeafEC;
	ListOfExecutionContext   mBlackHoleEC;

	ListOfExecutionContext   mBacktrackHitEC;

	ListOfExecutionContext mSliceableEC;
	ListOfExecutionContext mJumpPreservedEC;
	ListOfExecutionContext mJumpPreservedLeavesEC;

protected:
	ListOfExecutionContext::iterator ecIt;
	ListOfExecutionContext::iterator ecItEnd;

	ListOfExecutionContext::iterator itChildEC;
	ListOfExecutionContext::iterator endChildEC;

	ExecutionContext * tmpEC;
	ExecutionContext * prevEC;

	std::size_t leafOffset;
	std::size_t leafCount;

	std::size_t randomMax;

	std::size_t jumpOffset;
	Bitset jumpOffsetBitset;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmHitOrJumpProcessor(SymbexControllerUnitManager & aControllerUnitManager,
			const WObject * wfParameterObject)
	: RegisteredCoverageProcessorUnit(aControllerUnitManager, wfParameterObject,
			AVM_PRE_FILTERING_STAGE, PRECEDENCE_OF_HIT_OR_JUMP),
	mHitProcessor( nullptr ),

	mGlobalSearchScopeFlag( true ),
	mScheduler( AVM_OPCODE_SEQUENCE ),

	mFoldingFlag( true ),

	mJumpDelta( 1 ),
	mJumpHeight( mJumpDelta ),
	mJumpTrialsCount( 0 ),
	mJumpTrialsLimit( AVM_NUMERIC_MAX_SIZE_T ),

	mHitConsecutiveFlag( false ),
	mHitMaxFlag( false ),
	mHitLuckyFlag( false ),
	mBacktrackFlag( true ),

	mHitCount( 1 ),
	mJumpCount( 1 ),

	mHitFinalFlag( true ),
	mJumpSliceFlag( true ),

	mFinalCoverageStatistics( ),

	mGoalAchieved( false ),

	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	mAbsoluteStopContextFlag( false ),
	mHitCaseFlag( false ),

	mSelectionCount( 1 ),

	mInitialRootEC( ),
	mBufferLocalRootEC( ),

	mRelativeRootEC( ),
	mRelativeLeafEC( ),

	mAbsoluteLeafEC( ),
	mBlackHoleEC( ),

	mBacktrackHitEC( ),


	mSliceableEC( ),
	mJumpPreservedEC( ),
	mJumpPreservedLeavesEC( ),

	ecIt( ),
	ecItEnd( ),

	itChildEC( ),
	endChildEC( ),

	tmpEC( nullptr ),
	prevEC( nullptr ),

	leafOffset( 0 ),
	leafCount( 0 ),

	randomMax( 0 ),

	jumpOffset( 0 ),
	jumpOffsetBitset( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmHitOrJumpProcessor()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl() override;


	/**
	 * mScheduler
	 */
	inline bool isOrdered() const
	{
		return( mScheduler == AVM_OPCODE_PRIOR_GT );
	}

	inline bool isRegex() const
	{
		return( mScheduler == AVM_OPCODE_REGEX );
	}

	inline bool isUnordered() const
	{
		return( mScheduler == AVM_OPCODE_INTERLEAVING );
	}


	inline std::string strScheduler() const
	{
		return( OperatorLib::to_string(mScheduler) );
	}


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


	/**
	 * PROCESSOR REQUEST API :> CONITNUE , GOAL_ACHIEVED
	 */
	virtual void handleRequestContinue() override;

	virtual void handleRequestGoalAchieved() override;

	bool hojBacktrack();

	void hojSelection();
	void hojSelectionFinal();

	void updateRelativeLeaf();


	void updatePreserved();
	void jumpSlice();
	void jumpSliceBacktrack();
	void jumpSliceLucky();

	virtual bool postfilter() override;
	virtual bool postfilter(ExecutionContext & anEC) override;


	/**
	 * IHandlerEventDestroyCtx API
	 * Destroy Execution Context
	 */
	virtual void handleEventDestroyCtx(ExecutionContext * anEC) override;


	////////////////////////////////////////////////////////////////////////////
	// FINAL SLICING TOOLS
	////////////////////////////////////////////////////////////////////////////

	virtual bool isSliceableContext(ExecutionContext & anEC) const override;


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




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// AvmHitOrJumpObjective Information
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class HitOrJumpObjectiveInfo : public Element ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( HitOrJumpObjectiveInfo )
{

	AVM_DECLARE_CLONABLE_CLASS( HitOrJumpObjectiveInfo )


protected:
	/**
	 * ATTRIBUTES
	 */
	AvmCoverageStatistics mCoverageStatistics;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	HitOrJumpObjectiveInfo()
	: Element( CLASS_KIND_T( HitOrJumpObjectiveInfo ) ),
	mCoverageStatistics( )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	HitOrJumpObjectiveInfo(const HitOrJumpObjectiveInfo & hojInfo)
	: Element( hojInfo ),
	mCoverageStatistics( hojInfo.mCoverageStatistics )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~HitOrJumpObjectiveInfo()
	{
		//!! NOTHING
	}


	/**
	 * mCoverageStatistics
	 */
	AvmCoverageStatistics & getCoverageStatistics()
	{
		return mCoverageStatistics;
	}

	void setCoverageStatistics(
			AvmCoverageStatistics & aCoverageStatistics, std::size_t hitCount = 0)
	{
		mCoverageStatistics = aCoverageStatistics;

		mCoverageStatistics.addCoveredElement(hitCount);
	}

	void setCoverageStatistics(AvmCoverageStatistics & aCoverageStatistics,
			Bitset & coverageBitset, std::size_t hitCount = 0)
	{
		mCoverageStatistics = aCoverageStatistics;

		mCoverageStatistics.addCoveredElement(hitCount);

		mCoverageStatistics.mCoverageBitset = coverageBitset;
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & os) const override
	{
		//!!! NOTHING
	}

	void toFscn(OutStream & os) const
	{
		//!!! NOTHING
	}

};


} /* namespace sep */

#endif /* AVMHITORJUMPPROCESSOR_H_ */
