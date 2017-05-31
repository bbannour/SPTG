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

#ifndef HITORDEREDPROCESSOR_H_
#define HITORDEREDPROCESSOR_H_

#include "BaseHitProcessor.h"


namespace sep
{


class AvmHitOrJumpProcessor;
class ExecutionContext;
class EvaluationEnvironment;


class HitOrderedProcessor  :  public BaseHitProcessor
{

protected:
	/**
	 * ATTRIBUTE
	 */
	BF mLastObjective;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	HitOrderedProcessor(AvmHitOrJumpProcessor & hojProcessor,
			EvaluationEnvironment & anENV);

	/**
	 * DESTRUCTOR
	 */
	virtual ~HitOrderedProcessor()
	{
		//!! NOTHING
	}


	inline std::string strKind()
	{
		return( "ordered" );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure(WObject * wfParameterObject);

	virtual bool resetConfig();


	////////////////////////////////////////////////////////////////////////////
	// HIT FILTERING API
	////////////////////////////////////////////////////////////////////////////

	bool goalWillNeverAchieved(ExecutionContext * anEC);

	bool hit(avm_size_t jumpHeight);

	void hit(ExecutionContext * anEC,
			avm_size_t uncoveredOffset, avm_size_t hitCount);

	virtual void hitSelect(avm_size_t jumpOffset);


	// FILTERING TOOLS
	void saveBacktrackable(ExecutionContext * anEC, avm_size_t hitCount);

	bool willNeverReached(ExecutionContext * anEC, const BF & arg);


};


} /* namespace sep */

#endif /* HITORDEREDPROCESSOR_H_ */
