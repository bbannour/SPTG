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


	inline virtual std::string strKind() override
	{
		return( "ordered" );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure(const WObject * wfParameterObject) override;

	virtual bool resetConfig() override;


	////////////////////////////////////////////////////////////////////////////
	// HIT FILTERING API
	////////////////////////////////////////////////////////////////////////////

	virtual bool goalWillNeverAchieved(ExecutionContext & anEC) override;

	virtual bool hit(std::size_t jumpHeight) override;

	void hit(ExecutionContext & anEC,
			std::size_t uncoveredOffset, std::size_t hitCount);

	virtual void hitSelect(std::size_t jumpOffset) override;


	// FILTERING TOOLS
	void saveBacktrackable(ExecutionContext & anEC, std::size_t hitCount);

	bool willNeverReached(ExecutionContext & anEC, const BF & arg);


};


} /* namespace sep */

#endif /* HITORDEREDPROCESSOR_H_ */
