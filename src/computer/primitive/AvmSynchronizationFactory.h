/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMSYNCHRONIZATIONFACTORY_H_
#define AVMSYNCHRONIZATIONFACTORY_H_

#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/TableOfData.h>


namespace sep
{

class ArrayBF;
class BF;
class Router;

class Operator;

class RuntimeForm;


class AvmSynchronizationFactory
{

private:
	AvmSynchronizationFactory()
	{
		// NOTHING
	}

	virtual ~AvmSynchronizationFactory()
	{
		// NOTHING
	}


public:
	/*
	 * FUSION
	 * ExecutionData -- RuntimeForm
	 */
	static ExecutionData fusion(const ExecutionData & aRefED,
			const ExecutionData & firstED, const ExecutionData & sndED);

	static bool fusion(const ExecutionData & newED,
			const ParametersRuntimeForm & refParamsRF,
			const ParametersRuntimeForm & firstParamsRF,
			const ParametersRuntimeForm & sndParamsRF);

	static bool fusion(const ExecutionData & newED, const RuntimeForm & refRF,
			const RuntimeForm & firstRF, const RuntimeForm & sndRF);

	static bool fusion(RuntimeForm & aRF,
			const APTableOfData & refDataTable,
			const APTableOfData & firstDataTable,
			const APTableOfData & sndDataTable);

	static BF fusionArrayData(
			const RuntimeForm & aRF, ArrayBF * refArray,
			ArrayBF * firstArray, ArrayBF * sndArray);

	static bool fusion(RuntimeForm & aRF,
			const TableOfBufferT & refBufferTable,
			const TableOfBufferT & firstBufferTable,
			const TableOfBufferT & sndBufferTable);

	static bool fusion(RuntimeForm & aRF, const Router & refRouter,
			const Router & firstRouter, const Router & sndRouter);



	static BF syncBF(const Operator * buildOp, const BF & refBF,
			const BF & frstBF, const BF & sndBF);

	static BF buildScheduleForm(
			const Operator * buildOp, const BF & refScheduleForm,
			const BF & frstScheduleForm, const BF & sndScheduleForm);

	static BF buildRunnableElementTrace(const Operator * buildOp,
			const BF & refRunnableElementTrace,
			const BF & frstRunnableElementTrace,
			const BF & sndRunnableElementTrace);

	static BF buildIOElementTrace(
			const Operator * buildOp, const BF & refIOElementTrace,
			const BF & frstIOElementTrace, const BF & sndIOElementTrace);





};

}

#endif /* AVMSYNCHRONIZATIONFACTORY_H_ */
