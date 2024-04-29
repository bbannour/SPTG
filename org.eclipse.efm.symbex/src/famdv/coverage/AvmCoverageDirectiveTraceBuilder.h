/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_PROCESS_COVERAGE_AVMCOVERAGEDIRECTIVETRACEBUILDER_H_
#define AVM_PROCESS_COVERAGE_AVMCOVERAGEDIRECTIVETRACEBUILDER_H_

#include <collection/List.h>
#include <famcore/api/AvmCoverageHeuristicProperty.h>

#include <fml/buffer/LifoBuffer.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/InstanceOfBuffer.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>



namespace sep
{

class AvmCoverageTransitionView;
class OutStream;

class ExecutableForm;
class ExecutionContext;
class ExecutionData;

class InstanceOfMachine;
class InstanceOfPort;

class RuntimeForm;


class AvmTraceProperty  :  public TraceSequence
{

public:
	/**
	 * ATTRIBUTE
	 */
	AvmCoverageTransitionView * mTransitionCoverage;

	std::size_t mSize;

	std::size_t mUncoveredCount;

	std::size_t mGuardCount;

	std::size_t mUnconditionalCount;

	std::size_t mUnstableCount;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTraceProperty(AvmCoverageTransitionView * aTransitionCoverage)
	: TraceSequence( CLASS_KIND_T( AvmTraceProperty ) ),
	mTransitionCoverage( aTransitionCoverage ),
	mSize( 0 ),
	mUncoveredCount( 0 ),
	mGuardCount( 0 ),
	mUnconditionalCount( 0 ),
	mUnstableCount( 0 )
	{
		//!! NOTHING
	}

	AvmTraceProperty(ExecutionContext * anEC = nullptr)
	: TraceSequence( anEC ),
	mTransitionCoverage( nullptr ),
	mSize( 0 ),
	mUncoveredCount( 0 ),
	mGuardCount( 0 ),
	mUnconditionalCount( 0 ),
	mUnstableCount( 0 )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmTraceProperty(const TraceSequence & aTrace)
	: TraceSequence( aTrace ),
	mTransitionCoverage( nullptr ),
	mSize( 0 ),
	mUncoveredCount( 0 ),
	mGuardCount( 0 ),
	mUnconditionalCount( 0 ),
	mUnstableCount( 0 )
	{
		updadeSize();
	}

	AvmTraceProperty(const AvmTraceProperty & aTraceProperty)
	: TraceSequence( aTraceProperty ),
	mTransitionCoverage( aTraceProperty.mTransitionCoverage ),
	mSize( aTraceProperty.mSize ),
	mUncoveredCount( aTraceProperty.mUncoveredCount ),
	mGuardCount( aTraceProperty.mGuardCount ),
	mUnconditionalCount( aTraceProperty.mUnconditionalCount ),
	mUnstableCount( aTraceProperty.mUnstableCount )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTraceProperty()
	{
		//!! NOTHING
	}


	/**
	 * Configure
	 */
	inline bool configure(AvmTraceProperty & aTraceElement)
	{
		clear();

		mTransitionCoverage = aTraceElement.mTransitionCoverage;

		return( true );
	}


	/**
	 * Utils for TraceSequence
	 */
	void checkDecrementation(const AvmTransition * aTransition);

	void checkIncrementation(const AvmTransition * aTransition);


	inline void append(const RuntimeID & aRID, const AvmTransition * aTransition)
	{
		points.push_back( BF( new TracePoint(
				ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
				AVM_OPCODE_INVOKE_TRANSITION, aRID, aTransition) ) );

		++mSize;
		checkIncrementation( aTransition );
	}

	inline void clear()
	{
		points.clear();
		mSize = 0;
		mUncoveredCount = 0;
		mGuardCount = 0;
		mUnconditionalCount = 0;
		mUnstableCount = 0;
	}

	inline void copyTrace(AvmTraceProperty & aTraceElement)
	{
		TraceSequence::copyTrace( aTraceElement );

		mTransitionCoverage = aTraceElement.mTransitionCoverage;

		mSize = aTraceElement.mSize;
		mUncoveredCount = aTraceElement.mUncoveredCount;
		mGuardCount = aTraceElement.mGuardCount;
		mUnconditionalCount = aTraceElement.mUnconditionalCount;
		mUnstableCount = aTraceElement.mUnstableCount;
	}


	inline bool empty() const
	{
		return( mSize == 0 );
	}


	inline void pop_back(std::size_t ptsCount)
	{
		mSize = mSize - ptsCount;
		for( ; ptsCount > 0 ; --ptsCount )
		{
			checkDecrementation( backTransition() );

			points.pop_back();
		}
	}

	inline void pop_front(std::size_t ptsCount)
	{
		mSize = mSize - ptsCount;
		for( ; ptsCount > 0 ; --ptsCount )
		{
			checkDecrementation( frontTransition() );

			points.pop_front();
		}
	}

	inline void resize(std::size_t newSize)
	{
		if( newSize == 0 )
		{
			clear();
		}
		else for( ; mSize > newSize ; --mSize )
		{
			checkDecrementation( backTransition() );

			points.pop_back();
		}
	}


	/**
	 * mSize
	 * mUnconditionalCount
	 * mUnstableCount
	 */
	void updadeSize();


	inline std::size_t xSize() const
	{
//		return( mSize );
//		return( mSize - mUnconditionalCount );
//		return( mSize - mUnconditionalCount - mUnstableCount );

//		if( backTransition()->isUnstableTarget() )
//		{
//			return( 2 * mSize + mGuardCount -
//					mUncoveredCount - mUnconditionalCount - mUnstableCount );
//		}
//		else
		{
			return( mSize + mGuardCount -
					mUncoveredCount - mUnconditionalCount - mUnstableCount );
		}
	}


	bool compare( bool (* isComp)(std::size_t, std::size_t),
			const AvmTraceProperty & aTraceElement );

	template< class Compare >
	bool isInf(Compare isComp, const AvmTraceProperty & aTraceElement)
	{
		return( isComp(xSize(), aTraceElement.xSize()) );
	}

	template< class Compare >
	bool isSup(Compare isComp, const AvmTraceProperty & aTraceElement)
	{
		return( isComp(xSize(), aTraceElement.xSize()) );
	}


	inline bool sizeEQ(const AvmTraceProperty & aTraceElement) const
	{
		return( xSize() == aTraceElement.xSize() );
	}

	inline bool sizeGT(const AvmTraceProperty & aTraceElement) const
	{
		return( xSize() > aTraceElement.xSize() );
	}

	inline bool sizeGTE(const AvmTraceProperty & aTraceElement) const
	{
		return( xSize() >= aTraceElement.xSize() );
	}

	inline bool sizeLT(const AvmTraceProperty & aTraceElement) const
	{
		return( xSize() < aTraceElement.xSize() );
	}

	inline bool sizeLTE(const AvmTraceProperty & aTraceElement) const
	{
		return( xSize() <= aTraceElement.xSize() );
	}


	/**
	 * back / front;
	 * AvmTransition
	 */
	inline const AvmTransition * backTransition() const
	{
		return( points.back().to< TracePoint >().
				object->to_ptr< AvmTransition >() );
	}

	inline const AvmTransition * frontTransition() const
	{
		return( points.front().to< TracePoint >().
				object->to_ptr< AvmTransition >() );
	}

	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os, bool verbose = false) const;

	// Due to [-Woverloaded-virtual=]
	using Element::toStream;

};


DEFINE_LIST_REF( AvmTraceProperty )



class AvmCoverageDirectiveTraceBuilder  :  public IHeuristicClass
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef List< ListOfAvmTransition > ListOfListOfAvmTransition;


	/**
	 * ATTRIBUTE
	 */
	const ExecutionContext * mEC;
	ExecutionData mED;
	RuntimeID mRID;
	const AvmTransition * mTransition;

	TracePoint * mTransitionPoint;
	AvmTraceProperty mTraceElement;

	std::size_t mComputingPathCountLimit;
	std::size_t mComputingPathSizeLimit;

	bool mGoalAchievedFlag;

//	ListOfAvmTransition mTransitionPath;
//	ListOfInstanceOfPort mExpectedInput;
	InstanceOfBuffer mVirtualBuffer;
	LifoBuffer mEmitOutput;

	TableOfRuntimeFormState mTableOfRuntimeStatus;


	// computing variable for method << computePathToTransition >>
	ListOfListOfAvmTransition anyTransitionPaths;
	ListOfListOfAvmTransition prefixLoopTransitionPaths;

	ListOfAvmTransition outgoingTransitions;
	ListOfAvmTransition aTransitionPath;
	ListOfAvmTransition::const_iterator itTrans;
	ListOfAvmTransition::const_iterator endTrans;

	const InstanceOfMachine * tgtInstance;
	const ExecutableForm    * fwdMachine;
	const ExecutableForm    * tgtMachine;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageDirectiveTraceBuilder(
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 32, std::size_t pathSizeLimit = 32)
	: IHeuristicClass( anHeuristicClass ),
	mEC( nullptr ),
	mED( ),
	mRID( ),

	mTransition( nullptr ),
	mTransitionPoint( nullptr ),

	mTraceElement( ),

	mComputingPathCountLimit( pathCountLimit ),
	mComputingPathSizeLimit( pathSizeLimit ),

	mGoalAchievedFlag( false ),

	//mTransitionPath( ),
	//mExpectedInput( ),
	mVirtualBuffer(ExecutableForm::nullref(),
			Buffer::nullref(), 0, TYPE_LIFO_SPECIFIER, -1),
	mEmitOutput( mVirtualBuffer ),

	mTableOfRuntimeStatus( 0 ),

	// computing variable for method << computePathToTransition >>
	anyTransitionPaths( ),
	prefixLoopTransitionPaths( ),

	outgoingTransitions( ),
	aTransitionPath( ),
	itTrans( ),
	endTrans( ),

	tgtInstance( nullptr ),
	fwdMachine( nullptr ),
	tgtMachine( nullptr )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	AvmCoverageDirectiveTraceBuilder(
			const ExecutionContext * anEC, TracePoint * tpTransition,
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 64, std::size_t pathSizeLimit = 64);


	/**
	 * mComputingPathCountLimit
	 * mComputingPathSizeLimit
	 */
	void setComputingLimit(std::size_t pathCountLimit, std::size_t pathSizeLimit)
	{
		mComputingPathCountLimit = pathCountLimit;
		mComputingPathSizeLimit  = pathSizeLimit;
	}


	////////////////////////////////////////////////////////////////////////////
	// Configure
	////////////////////////////////////////////////////////////////////////////

	bool configure(AvmTraceProperty & aTraceElement,
			const ExecutionContext * anEC, TracePoint * tpTransition,
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 64, std::size_t pathSizeLimit = 64);

	bool configure(AvmTraceProperty & aTraceElement,
			const ExecutionContext * anEC,
			const RuntimeID & aRID, const AvmTransition * aTransition,
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 16, std::size_t pathSizeLimit = 16);


	////////////////////////////////////////////////////////////////////////////
	// API
	////////////////////////////////////////////////////////////////////////////

	bool initialize();

	bool computePath();

	bool computePath(AvmTraceProperty & aTraceElement);

	bool computePath(AvmTraceProperty & aTraceElement, ExecutionContext * anEC,
			const RuntimeID & aRID, const AvmTransition * aTransition,
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_SMART_CLASS,
			std::size_t pathCountLimit = 16, std::size_t pathSizeLimit = 16);

	void report(OutStream & os);


	bool computePath(const RuntimeID & aRID, const AvmTransition * aTransition);

	bool fireTransition(const RuntimeID & aRID, const AvmTransition * aTransition);

	void traceTransition(const RuntimeID & aRID, const AvmTransition * aTransition);

	bool computePathToTransition(
			const RuntimeID & aRID, const AvmTransition * aTransition);


	inline bool computePathFromRunnable(
			const RuntimeID & aRID, const AvmTransition * aTransition)
	{
		switch( mHeuristicClass )
		{
			case IHeuristicClass::HEURISTIC_BASIC_CLASS:
			{
				return( computeBasicPathFromRunnable(aRID, aTransition) );
			}

			case IHeuristicClass::HEURISTIC_NAIVE_CLASS:
			case IHeuristicClass::HEURISTIC_SMART_CLASS:
			case IHeuristicClass::HEURISTIC_AGRESSIVE_CLASS:
			case IHeuristicClass::HEURISTIC_NOTHING_ELSE_CLASS:
			default:
			{
				return( computeSmartPathFromRunnable(aRID, aTransition) );
			}
		}
	}

	bool computeBasicPathFromRunnable(
			const RuntimeID & aRID, const AvmTransition * aTransition);

	bool computeSmartPathFromRunnable(
			const RuntimeID & aRID, const AvmTransition * aTransition);


	bool computePathToInput(
			const RuntimeID & aRID, const InstanceOfPort * anInputTrace);


	bool computePathToTransition(
			const RuntimeID & aRID, const AvmTransition * aTransition,
			ListOfAvmTransition & oneTransitionPath);

	bool computePathToTransition(
			const RuntimeID & aRID, const AvmTransition * aTransition,
			ListOfListOfAvmTransition & allTransitionPaths);

	void computeTargetMachine(RuntimeID & aRID, AvmCode * aCode);

};


} /* namespace sep */

#endif /* AVM_PROCESS_COVERAGE_AVMCOVERAGEDIRECTIVETRACEBUILDER_H_ */
