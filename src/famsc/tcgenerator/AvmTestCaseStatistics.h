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

#ifndef AVM_TESTCASE_STATISTICS_H_
#define AVM_TESTCASE_STATISTICS_H_

#include <common/BF.h>


namespace sep
{

class AvmPathGuidedTestcaseGenerator;
class EvaluationEnvironment;
class Transition;


class AvmTestCaseStatistics
{


public:
	/**
	 * ATTRIBUTES
	 */
	AvmPathGuidedTestcaseGenerator & mProcessor;
	EvaluationEnvironment & ENV;

	BF mLargestGuardCondition;
	const Transition * mSelectedTransition;

	uint32_t mMaxSize;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTestCaseStatistics(AvmPathGuidedTestcaseGenerator & aProcessor,
			EvaluationEnvironment & anENV)
	: mProcessor(aProcessor),
	ENV( anENV ),
	mLargestGuardCondition( ),
	mSelectedTransition( nullptr ),
	mMaxSize( 0 )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTestCaseStatistics()
	{
		//!! NOTHING
	}


public:
	void takeAccount(const BF & aGuard, const Transition * aTransition);

	void saveGuardCondition() const;

	void reportDefault(OutStream & os) const;


};


} /* namespace sep */

#endif /* AVM_TESTCASE_STATISTICS_H_ */
