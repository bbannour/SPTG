/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 janv. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXECUTIONDATAFACTORY_H_
#define EXECUTIONDATAFACTORY_H_

#include <common/BF.h>

#include <computer/BaseEnvironment.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


class ExecutionDataFactory
{
public:


	/*
	 * SETTER
	 * RunnableElementTrace
	 * IOElementTrace
	 */
	static void appendRunnableElementTrace(
			APExecutionData & apED, const BF & aRunnableElementTrace);

	static void appendIOElementTrace(
			APExecutionData & apED, const BF & theIOElementTrace);


	/**
	 * COMPARISON
	 */
	static bool equalsStatus(
			const ExecutionData & oneED, const ExecutionData & otherED);

	static bool equalsData(
			const ExecutionData & oneED, const ExecutionData & otherED);




};



} /* namespace sep */
#endif /* EXECUTIONDATAFACTORY_H_ */
