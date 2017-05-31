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

#include <fam/coverage/BaseCoverageFilter.h>
#include <sew/SymbexEventManager.h>

#include <collection/Bitset.h>

#include <fml/operator/OperatorLib.h>

#include <fam/coverage/AvmCoverageStatistics.h>


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

	AVM_OPCODE scheduler;

	bool mFoldingFlag;

	avm_size_t mJumpDelta;
	avm_size_t mJumpHeight;

	avm_size_t mJumpTrialsCount;
	avm_size_t mJumpTrialsLimit;

	bool mHitConsecutiveFlag;
	bool mHitMaxFlag;
	bool mHitLuckyFlag;
	bool mBacktrackFlag;

	avm_size_t mHitCount;
	avm_size_t mJumpCount;

	bool mHitFinalFlag;


	bool mJumpSliceFlag;

	AvmCoverageStatistics mFinalCoverageStatistics;

	bool mGoalAchieved;


	////////////////////////////////////////////////////////////////////////////
	// Computing Variables
	bool mAbsoluteStopContextFlag;

	bool mHitCaseFlag;

	avm_size_t mSelectionCount;

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

	avm_size_t leafOffset;
	avm_size_t leafCount;

	avm_size_t randomMax;

	avm_size_t jumpOffset;
	Bitset jumpOffsetBitset;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmHitOrJumpProcessor(SymbexControllerUnitManager & aControllerUnitManager,
			WObject * wfParameterObject)
	: RegisteredCoverageProcessorUnit(aControllerUnitManager, wfParameterObject,
			AVM_PRE_FILTERING_STAGE, PRECEDENCE_OF_HIT_OR_JUMP),
	mHitProcessor( NULL ),

	mGlobalSearchScopeFlag( true ),
	scheduler( AVM_OPCODE_SEQUENCE ),

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

	tmpEC( NULL ),
	prevEC( NULL ),

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

	virtual bool configureImpl();


	/**
	 * scheduler
	 */
	inline bool isOrdered() const
	{
		return( scheduler == AVM_OPCODE_PRIOR_GT );
	}

	inline bool isRegex() const
	{
		return( scheduler == AVM_OPCODE_REGEX );
	}

	inline bool isUnordered() const
	{
		return( scheduler == AVM_OPCODE_INTERLEAVING );
	}


	inline std::string strScheduler() const
	{
		return( OperatorLib::to_string(scheduler) );
	}


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void reportMinimum(OutStream & os) const;

	virtual void reportDefault(OutStream & os) const;

	////////////////////////////////////////////////////////////////////////////
	// NON-REGRESSION TEST API
	////////////////////////////////////////////////////////////////////////////

	virtual void tddRegressionReportImpl(OutStream & os);


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

//	virtual bool preprocess();
//
//	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////

	virtual bool filteringInitialize();

	virtual bool prefilter();
	virtual bool prefilter(ExecutionContext & anEC);


	/**
	 * PROCESSOR REQUEST API :> CONITNUE , GOAL_ACHIEVED
	 */
	virtual void handleRequestContinue();

	virtual void handleRequestGoalAchieved();

	bool hojBacktrack();

	void hojSelection();
	void hojSelectionFinal();

	void updateRelativeLeaf();


	void updatePreserved();
	void jumpSlice();
	void jumpSliceBacktrack();
	void jumpSliceLucky();

	virtual bool postfilter();
	virtual bool postfilter(ExecutionContext & anEC);


	/**
	 * IHandlerEventDestroyCtx API
	 * Destroy Execution Context
	 */
	virtual void handleEventDestroyCtx(ExecutionContext * anEC);


	////////////////////////////////////////////////////////////////////////////
	// FINAL SLICING TOOLS
	////////////////////////////////////////////////////////////////////////////

	virtual bool isSliceableContext(ExecutionContext & anEC) const;


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	inline virtual void toStream(OutStream & os) const
	{
		if( mParameterWObject != NULL )
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

class HitOrJumpObjectiveInfo :
		public Element ,
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
			AvmCoverageStatistics & aCoverageStatistics, avm_size_t hitCount = 0)
	{
		mCoverageStatistics = aCoverageStatistics;

		mCoverageStatistics.addCoveredElement(hitCount);
	}

	void setCoverageStatistics(AvmCoverageStatistics & aCoverageStatistics,
			Bitset & coverageBitset, avm_size_t hitCount = 0)
	{
		mCoverageStatistics = aCoverageStatistics;

		mCoverageStatistics.addCoveredElement(hitCount);

		mCoverageStatistics.mCoverageBitset = coverageBitset;
	}


	/**
	 * Serialization
	 */
	void toStream(OutStream & os) const
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
