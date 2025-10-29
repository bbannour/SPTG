/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef STATEMACHINEREACHABILITY_H_
#define STATEMACHINEREACHABILITY_H_

#include <collection/Typedef.h>


namespace sep
{


class AvmProgram;
class BaseCoverageFilter;
class Configuration;
class InstanceOfMachine;


class StatemachineReachability
{

protected:
	/**
	 * ATTRIBUTES
	 */
	BaseCoverageFilter & mCoverageFilter;

	std::size_t mBackwardAnalysisLookaheadDepth;
	std::size_t mForwardAnalysisLookaheadDepth;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	StatemachineReachability(BaseCoverageFilter & aCoverageFilter)
	: mCoverageFilter( aCoverageFilter ),
	mBackwardAnalysisLookaheadDepth( AVM_NUMERIC_MAX_SIZE_T ),
	mForwardAnalysisLookaheadDepth ( AVM_NUMERIC_MAX_SIZE_T )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~StatemachineReachability()
	{
		//!! NOTHING
	}


	/**
	 * Reachability Analysis
	 */
	inline bool computeReachableComponent(
			const Configuration & aConfiguration,
			std::size_t aBackwardAnalysisLookaheadDepth)
	{
		mBackwardAnalysisLookaheadDepth = aBackwardAnalysisLookaheadDepth;

		bool isOK = computeBackwardReachableComponent( aConfiguration );

		return( computeForwardReachableComponent(aConfiguration) || isOK );
	}


	/**
	 * Backward Reachability Analysis
	 */
	bool computeBackwardReachableComponent(const Configuration & aConfiguration);

	void computeBackwardReachableComponent(
			const Configuration & aConfiguration, ExecutableForm * aState,
			ListOfExecutableForm & aListOfTreatedStates,
			std::size_t theCurentBackwardDepth);


	/**
	 * Forward Reachability Analysis
	 */
	bool computeForwardReachableComponent(const Configuration & aConfiguration);

	void computeForwardReachableComponent(ExecutableForm * execMachine,
			ListOfExecutableForm & aTraceMachine, ExecutableForm * fwdMachine);

};

} /* namespace sep */
#endif /* STATEMACHINEREACHABILITY_H_ */
