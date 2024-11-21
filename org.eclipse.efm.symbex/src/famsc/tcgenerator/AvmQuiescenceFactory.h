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

#ifndef AVM_QUIESCENCE_FACTORY_H_
#define AVM_QUIESCENCE_FACTORY_H_

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/expression/AvmCode.h>

#include <fml/infrastructure/Port.h>

#include <fml/symbol/Symbol.h>


namespace sep
{

class AbstractProcessorUnit;
class ExecutionContext;


class AvmQuiescenceFactory
{

public:
	/**
	 * ATTRIBUTE
	 */
	AbstractProcessorUnit & mProcessor;

	BF INFO_QUIESCENCE;
	BF INFO_NON_QUIESCENCE;

	uint32_t mNoQuiecenceNumber;

	Port mQuiescenceAstPort;

	Symbol mQuiescencePort;

	BFCode mQuiescenceElementTrace;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmQuiescenceFactory(AbstractProcessorUnit & aProcessor);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmQuiescenceFactory()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 */
	const Symbol & getQuiescencePort()
	{
		return mQuiescencePort;
	}

	////////////////////////////////////////////////////////////////////////////
	// QUIESCENCE
	////////////////////////////////////////////////////////////////////////////

	void buildGraph();

	bool recQuiescenceOf(ExecutionContext & anEC);

	bool quiescenceOf(ExecutionContext & anEC);

	BF computeQuiescenceCondition(const ExecutionContext & tcSourceEC);

	BF computeAdmissibleQuiescenceCondition(const ExecutionContext & tcSourceEC);

	void removeUnsatisfiableQuiescence(ExecutionContext * anEC);

};


} /* namespace sep */

#endif /* AVM_QUIESCENCE_FACTORY_H_ */
