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

#include "AvmTestCaseStatistics.h"
#include "AvmPathGuidedTestcaseGenerator.h"

#include <fml/infrastructure/Machine.h>
#include <fml/infrastructure/Transition.h>

#include <solver/api/SolverFactory.h>

namespace sep
{


void AvmTestCaseStatistics::takeAccount(
		const BF & aGuardCondition, const Transition * aTransition)
{
	const std::string strGuard = aGuardCondition.str();
	if( mMaxSize < strGuard.size() )
	{
		mMaxSize = strGuard.size();
		mLargestGuardCondition = aGuardCondition;
		mSelectedTransition = aTransition;
	}
}


void AvmTestCaseStatistics::saveGuardCondition() const
{
	OutStream & out = mProcessor.newFileStream("biguest_condition.z3");

	out << ";; z3 -st " << mProcessor.getFolder().location << "/biguest_condition.z3"
		<< std::endl;

	if( mSelectedTransition != nullptr )
	{
		SolverFactory::to_smt(out, mLargestGuardCondition);
	}

}

void AvmTestCaseStatistics::reportDefault(OutStream & os) const
{
	if( mSelectedTransition != nullptr )
	{
		saveGuardCondition();

		os << EMPHASIS("The transition with the largest guard condition");
		os << mSelectedTransition->getSource().getNameID() << " :";
		mSelectedTransition->toStream(os);
	}
}



} /* namespace sep */
