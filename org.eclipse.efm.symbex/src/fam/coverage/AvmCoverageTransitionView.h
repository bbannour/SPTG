/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCOVERAGETRANSITIONVIEW_H_
#define AVMCOVERAGETRANSITIONVIEW_H_

#include "AvmCoverageAbstractView.h"

#include <collection/Bitset.h>
#include <collection/Typedef.h>

#include <fml/common/SpecifierElement.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

class WaitingStrategy;
class AvmCoverageProcessor;
class OutStream;
class AvmTransition;

class ExecutionContext;
class ExecutionData;

class RuntimeForm;
class RuntimeID;


class AvmCoverageTransitionView  :  public AvmCoverageAbstractView
{

	AVM_DECLARE_CLONABLE_CLASS( AvmCoverageTransitionView )


protected:
	/**
	 * ATTRIBUTES
	 */
	Specifier::DESIGN_KIND mScope;

	// Table des flag de couverture de transition pour chaque INSTANCE de machine
	ArrayOfBitset * mExecutableCoverageTable;
	ArrayOfBitset * mTransitionCoverageTable;

	VectorOfExecutableForm mTableofRuntimeExecutable;

	// Computing Local Variables
	Bitset * tmpRuntimeTransitionBitset;

	ExecutionContext * mDirectiveHitEC;
	bool mDirectiveFailedFlag;

	VectorOfExecutionContext mCertainlyHitEC;
	avm_size_t mCertainlyFireableTransitionCount;
	avm_size_t tmpCertainlyFireableTransitionCount;

	VectorOfExecutionContext mStronglyHitEC;
	avm_size_t mStronglyFireableTransitionCount;
	avm_size_t tmpStronglyFireableTransitionCount;

	VectorOfExecutionContext mWeaklyHitEC;
	avm_size_t mWeaklyFireableTransitionCount;
	avm_size_t tmpWeaklyFireableTransitionCount;

	ListOfExecutionContext mWaitingQueue;

	avm_offset_t offset;
	avm_offset_t endOffset;

	avm_offset_t maxRandomOffset;
	Bitset randomOffsetBitset;

	ExecutionContext * tmpEC;
	ExecutableForm * tmpEF;
	RuntimeID itRID;
	TableOfRuntimeT::const_iterator itRF;
	TableOfRuntimeT::const_iterator endRF;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageTransitionView(AvmCoverageProcessor & aCoverageProcessor,
			WObject * wfParameterObject)
	: AvmCoverageAbstractView( aCoverageProcessor , wfParameterObject ),
	mScope( Specifier::DESIGN_MODEL_KIND ),

	mExecutableCoverageTable( NULL ),
	mTransitionCoverageTable( NULL ),
	mTableofRuntimeExecutable( ),

	// Computing Local Variables
	tmpRuntimeTransitionBitset( NULL ),

	mDirectiveHitEC( NULL ),
	mDirectiveFailedFlag( false ),

	mCertainlyHitEC( ),
	mCertainlyFireableTransitionCount( 0 ),
	tmpCertainlyFireableTransitionCount( 0 ),

	mStronglyHitEC( ),
	mStronglyFireableTransitionCount( 0 ),
	tmpStronglyFireableTransitionCount( 0 ),

	mWeaklyHitEC( ),
	mWeaklyFireableTransitionCount( 0 ),
	tmpWeaklyFireableTransitionCount( 0 ),

	mWaitingQueue( ),

	offset( 0 ),
	endOffset( 0 ),

	maxRandomOffset( 0 ),
	randomOffsetBitset( ),

	tmpEC( NULL ),
	tmpEF( NULL ),
	itRID( ),
	itRF( ),
	endRF( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageTransitionView();


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// COVERAGE PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configureImpl();

	void configureExecutableCoverageTableFlag(bool value);
	void configureExecutableCoverageTableFlag(
			ExecutableForm * anExecutable, bool value);

	void configureInstanceCoverageTableFlag();
	void configureInstanceCoverageTableFlag(bool value);
	void configureInstanceCoverageTableFlag(
			const ExecutionData & anED, const RuntimeID & aRID, bool value);

	void configureTransitionCoverageTableFlag(
			ListOfAvmTransition & listOfTransition, bool value);


	Bitset * getCoverageTableBitset(const RuntimeID & aRID);


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////

	virtual void reportMinimum(OutStream & os) const;

	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////

//$	virtual bool preprocess();
//
//	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// PROCESSOR FILTERING API
	////////////////////////////////////////////////////////////////////////////

	bool prefiltering(ListOfExecutionContext & ecQueue);

	bool postfiltering(ListOfExecutionContext & ecQueue);

	virtual void updateCoverageTable(ExecutionContext * anEC);


	/**
	 * Heuristic << High Priority Context >> implementation
	 * REQUEUE_WAITING part
	 */
	bool computeHighPriorityContext(ListOfExecutionContext & ecQueue,
			WaitingStrategy & aWaitingStrategy);

	bool highRequeueWaitingTable(WaitingStrategy & aWaitingStrategy,
			avm_uint8_t aWeightMin, avm_uint8_t aWeightMax);

	/**
	 * Heuristic << Any Priority Context >> implementation
	 * REQUEUE_WAITING part
	 */
	bool computePriorityContext(ListOfExecutionContext & ecQueue,
			WaitingStrategy & aWaitingStrategy);

	bool elseRequeueWaitingTable(WaitingStrategy & aWaitingStrategy,
			avm_uint8_t aWeightMin, avm_uint8_t aWeightMax);


	/**
	 * UTILS
	 */
	void setHitWeight(VectorOfExecutionContext & hitEC,
			avm_uint8_t hitWeight, bool randomFlag, avm_size_t hitCount);

	void computeWeight(ExecutionContext * anEC);
	void computeWeightNaive(ExecutionContext * anEC);
	void computeWeightSmart(ExecutionContext * anEC);
	void computeWeightAgressive(ExecutionContext * anEC);


	bool checkNonPriorityWeight(ExecutionContext * anEC);

	void computePriorityWeight(ExecutionContext * anEC);

	bool checkCertainlyPriorityWeight(ExecutionContext * anEC);
	bool checkStronglyPriorityWeight(ExecutionContext * anEC);
	bool checkWeaklyPriorityWeight(ExecutionContext * anEC);


	void computeWeightOfResult(const ListOfExecutionContext & ecQueue);


	avm_uint8_t checkFireability(const ExecutionData & anED,
			const RuntimeID & aRID, AvmTransition * aTransition);

	void computeFireability(const ExecutionData & anED,
			const RuntimeID & aRID, AvmTransition * aTransition);

	void traceFireability(OutStream & os, const ExecutionData & anED,
			const RuntimeID & aRID, AvmTransition * aTransition);


	bool isControlLoop(ExecutionContext * anEC);
	bool isSyntaxicLoop(ExecutionContext * anEC);
	bool isTrivialLoop(ExecutionContext * anEC);

	void fireableTransitionCount(
			const ExecutionData & anED, const RuntimeID & aRID);

	void fireableTransitionCount(const ExecutionData & anED);

	void fireableTransitionCount(
			const ExecutionData & anED, const RuntimeForm & aRF);

	void fireableTransitionTrace(OutStream & os, const ExecutionData & anED);

	void fireableTransitionTrace(OutStream & os,
			const ExecutionData & anED, const RuntimeForm & aRF);

	void updateTransitionCoverageTable(
			ExecutionContext * anEC, const BF & aFiredCode);

	void updateTransitionCoverageTable(ExecutionContext * anEC,
			const RuntimeID & aRID, AvmTransition * firedTransition);

	bool testTransitionCoverage(AvmTransition * firedTransition);


	/**
	 * Collect uncovered transition
	 */
	// Update uncovered table
	void updateUncoveredTransition(
			VectorOfAvmTransition & aTableofUncoveredTransition);

	// Collect all uncovered
	void collectUncoveredTransition(
			VectorOfAvmTransition & aTableofUncoveredTransition);

	// Collect uncovered in a given context
	void collectUncoveredTransition(const ExecutionData & anED,
			VectorOfAvmTransition & listofTransition);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	virtual void toStream(OutStream & os) const
	{
		//!! NOTHING
	}

};

} /* namespace sep */

#endif /* AVMCOVERAGETRANSITIONVIEW_H_ */
