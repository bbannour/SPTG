/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCOVERAGEHEURISTICPROPERTY_H_
#define AVMCOVERAGEHEURISTICPROPERTY_H_

#include <string>

#include <util/avm_numeric.h>

#include <fml/common/SpecifierElement.h>


namespace sep
{

class WObject;


/**
 * Execution Context Heuristic Weight
 */
class IHeuristicContextWeight
{

public:
	enum ENUM_HEURISTIC_CLASS
	{
		WEIGHT_SELECTED_ACHIEVABLE   = 0,

		WEIGHT_CERTAINLY_ACHIEVABLE  = 1,
		WEIGHT_STRONGLY_ACHIEVABLE   = 2,
		WEIGHT_WEAKLY_ACHIEVABLE     = 3,

		WEIGHT_NON_PRIORITY          = 4,
		WEIGHT_UNKNOWN_ACHIEVABLE    = 5,

		WEIGHT_NON_ACHIEVABLE        = 6,
	};


	static std::string strHeuristicWeight(std::uint8_t aWeight);

};


/**
 * Heuristic class
 */
class IHeuristicClass
{

public:

	enum ENUM_HEURISTIC_CLASS
	{
		HEURISTIC_BASIC_CLASS,

		HEURISTIC_NAIVE_CLASS,

		HEURISTIC_SMART_CLASS,

		HEURISTIC_AGRESSIVE_CLASS,

		HEURISTIC_NOTHING_ELSE_CLASS
	};


	/*
	 * ATTRIBUTES
	 */
	ENUM_HEURISTIC_CLASS mHeuristicClass;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	IHeuristicClass(
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_BASIC_CLASS)
	: mHeuristicClass( anHeuristicClass )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	IHeuristicClass(const IHeuristicClass & aHeuristic)
	: mHeuristicClass( aHeuristic.mHeuristicClass )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~IHeuristicClass()
	{
		//!! NOTHING
	}


	/**
	 * SETTER
	 * mHeuristicClass
	 */
	static ENUM_HEURISTIC_CLASS incrHeuristicClass(
			ENUM_HEURISTIC_CLASS anHeuristicClass);

	inline void incrHeuristicClass()
	{
		mHeuristicClass = incrHeuristicClass( mHeuristicClass );
	}


	inline void resetHeuristicClass(
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_BASIC_CLASS)
	{
		mHeuristicClass = anHeuristicClass;
	}


	static std::string strHeuristicClass(ENUM_HEURISTIC_CLASS anHeuristicClass);

	inline std::string strHeuristicClass() const
	{
		return( strHeuristicClass(mHeuristicClass) );
	}

	static ENUM_HEURISTIC_CLASS toHeuristicClass(
			const std::string & strHeuristicClass);

};



/*
 * The General Coverage Heuristic Property
 */
class AvmCoverageHeuristicProperty  :  public IHeuristicClass
{

public:
	/*
	 * ATTRIBUTES
	 */
	Specifier::DESIGN_KIND mScope;

	bool mHeuristicEnabled;
	std::size_t mHeuristicTrialsLimit;
	std::size_t mHeuristicTrialsCount;

	std::size_t mCoverageRateGoal;
	std::size_t mCoverageRestGoal;

	ENUM_HEURISTIC_CLASS mDirectiveTraceHeuristicClass;
	std::size_t mDirectiveTraceCountLimit;
	std::size_t mDirectiveTraceSizeLimit;

	std::size_t mCoverageHeightPeriod;
	std::size_t mCoverageHeight;

	std::size_t mCoverageHeightReachedCount;
	std::size_t mCoverageHeightReachedLimit;
	bool       mCoverageHeightReachedFlag;

	bool       mHitCertainlyRandomFlag;
	std::size_t mHitCertainlyCount;

	bool       mHitStronglyRandomFlag;
	std::size_t mHitStronglyCount;

	bool       mHitWeaklyRandomFlag;
	std::size_t mHitWeaklyCount;

	bool       mHitOtherRandomFlag;
	std::size_t mHitOtherCount;


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageHeuristicProperty(
			ENUM_HEURISTIC_CLASS anHeuristicClass = HEURISTIC_BASIC_CLASS)
	: IHeuristicClass( anHeuristicClass ),

	mScope( Specifier::DESIGN_MODEL_KIND ),

	mHeuristicEnabled( true ),

	mHeuristicTrialsLimit( 7 ),
	mHeuristicTrialsCount( 0 ),

	mCoverageRateGoal( 100 ),
	mCoverageRestGoal( 0 ),

	mDirectiveTraceHeuristicClass( HEURISTIC_SMART_CLASS ),
	mDirectiveTraceCountLimit( 8 ),
	mDirectiveTraceSizeLimit( 8 ),

	mCoverageHeightPeriod( 0 ),
	mCoverageHeight( 0 ),

	mCoverageHeightReachedCount( 0 ),
	mCoverageHeightReachedLimit( 1 ),
	mCoverageHeightReachedFlag( false ),

	mHitCertainlyRandomFlag( false ),
	mHitCertainlyCount( 1 ),

	mHitStronglyRandomFlag( false ),
	mHitStronglyCount( 1 ),

	mHitWeaklyRandomFlag( false ),
	mHitWeaklyCount( 1 ),

	mHitOtherRandomFlag( false ),
	mHitOtherCount( 1 )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmCoverageHeuristicProperty(const AvmCoverageHeuristicProperty & aCHP)
	: IHeuristicClass( aCHP ),

	mScope( aCHP.mScope ),

	mHeuristicEnabled( aCHP.mHeuristicEnabled ),

	mHeuristicTrialsLimit( aCHP.mHeuristicTrialsLimit ),
	mHeuristicTrialsCount( aCHP.mHeuristicTrialsCount ),

	mCoverageRateGoal( aCHP.mCoverageRateGoal ),
	mCoverageRestGoal( aCHP.mCoverageRestGoal ),

	mDirectiveTraceHeuristicClass( aCHP.mDirectiveTraceHeuristicClass ),
	mDirectiveTraceCountLimit( aCHP.mDirectiveTraceCountLimit ),
	mDirectiveTraceSizeLimit( aCHP.mDirectiveTraceSizeLimit ),

	mCoverageHeightPeriod( aCHP.mCoverageHeightPeriod ),
	mCoverageHeight( aCHP.mCoverageHeight ),

	mCoverageHeightReachedCount( aCHP.mCoverageHeightReachedCount ),
	mCoverageHeightReachedLimit( aCHP.mCoverageHeightReachedLimit ),
	mCoverageHeightReachedFlag( aCHP.mCoverageHeightReachedFlag ),

	mHitCertainlyRandomFlag( aCHP.mHitCertainlyRandomFlag ),
	mHitCertainlyCount( aCHP.mHitCertainlyCount ),

	mHitStronglyRandomFlag( aCHP.mHitStronglyRandomFlag ),
	mHitStronglyCount( aCHP.mHitStronglyCount ),

	mHitWeaklyRandomFlag( aCHP.mHitWeaklyRandomFlag ),
	mHitWeaklyCount( aCHP.mHitWeaklyCount ),

	mHitOtherRandomFlag( aCHP.mHitOtherRandomFlag ),
	mHitOtherCount( aCHP.mHitOtherCount )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageHeuristicProperty()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure(const WObject * wfParameterObject);

};


} /* namespace sep */

#endif /* AVMCOVERAGEHEURISTICPROPERTY_H_ */
