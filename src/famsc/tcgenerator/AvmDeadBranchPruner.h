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

#ifndef AVM_DEAD_BRANCH_PRUNER
#define AVM_DEAD_BRANCH_PRUNER

#include <common/BF.h>

#include <fml/executable/InstanceOfData.h>


namespace sep
{

class AbstractProcessorUnit;
class ExecutionContext;


class AvmDeadBranchPruner
{

public:
	/**
	 * ATTRIBUTE
	 */
	AbstractProcessorUnit & mProcessor;

	BF INFO_DEAD_BRANCH_PRUNED;

	const ExecutionContext * mTestPurposePassEC;

	InstanceOfData::Table mNewfreshInitialParams;

	uint32_t mDeadBranchNumber;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmDeadBranchPruner(AbstractProcessorUnit & aProcessor);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmDeadBranchPruner()
	{
		//!! NOTHING
	}

	////////////////////////////////////////////////////////////////////////////
	// DETERMINISM
	////////////////////////////////////////////////////////////////////////////

	void pruneDeadBranch();

	void pruneDeadBranch(ExecutionContext & anEC);

	bool isDeadBranch(ExecutionContext & anEC);

};


} /* namespace sep */

#endif /* AVM_DEAD_BRANCH_PRUNER */
