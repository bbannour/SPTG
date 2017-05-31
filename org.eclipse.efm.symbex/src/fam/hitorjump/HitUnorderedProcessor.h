/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 31 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef HITUNORDEREDPROCESSOR_H_
#define HITUNORDEREDPROCESSOR_H_

#include "BaseHitProcessor.h"

#include <collection/Bitset.h>


namespace sep
{


class AvmHitOrJumpProcessor;
class ExecutionContext;
class EvaluationEnvironment;


class HitUnorderedProcessor  :  public BaseHitProcessor
{


protected:
	/**
	 * ATTRIBUTE
	 */
	VectorOfBitset        mHitCoverageBitset;

	VectorOfBitset        mHitSelectedCoverageBitset;

	VectorOfExecutionContext mHitSelectedEC;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	HitUnorderedProcessor(AvmHitOrJumpProcessor & hojProcessor,
			EvaluationEnvironment & anENV);

	/**
	 * DESTRUCTOR
	 */
	virtual ~HitUnorderedProcessor()
	{
		//!! NOTHING
	}


	inline std::string strKind()
	{
		return( "unordered" );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool resetConfig();


	////////////////////////////////////////////////////////////////////////////
	// HIT FILTERING API
	////////////////////////////////////////////////////////////////////////////

	bool goalWillNeverAchieved(ExecutionContext * anEC);

	bool hit(avm_size_t jumpHeight);

	void hit(ExecutionContext * anEC,
			Bitset coverageBitset,	avm_size_t hitCount);


	virtual void hitSelect(avm_size_t jumpOffset);

	Bitset & hitCoverageBitset(ExecutionContext * anEC);


	// FILTERING TOOLS
	void saveBacktrackable(ExecutionContext * anEC,
			Bitset & coverageBitset, avm_size_t hitCount);

	bool willNeverHit(ExecutionContext * anEC, Bitset & coverageBitset);

};


} /* namespace sep */

#endif /* HITUNORDEREDPROCESSOR_H_ */
