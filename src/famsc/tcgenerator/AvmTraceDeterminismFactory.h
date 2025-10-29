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

#ifndef AVM_TRACE_DETERMINISM_FACTORY
#define AVM_TRACE_DETERMINISM_FACTORY

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{

class AbstractProcessorUnit;
class ExecutionContext;


class AvmTraceDeterminismFactory
{

public:
	/**
	 * ATTRIBUTE
	 */
	AbstractProcessorUnit & mProcessor;

	BF INFO_DETERMINISTIC;
	BF INFO_NON_DETERMINISTIC;

	InstanceOfData::Table mNewfreshInitialParams;

	uint32_t mNonDeterministicNumber;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmTraceDeterminismFactory(AbstractProcessorUnit & aProcessor);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmTraceDeterminismFactory()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// DETERMINISM
	////////////////////////////////////////////////////////////////////////////

	bool checkDeterminism();

	bool checkDeterminism(ExecutionContext & anEC);

	bool checkDeterminism(ExecutionContext & tpEC,
			const InstanceOfPort & comPort, const ExecutionContext & aTargetEC);

};


} /* namespace sep */

#endif /* AVM_TRACE_DETERMINISM_FACTORY */
