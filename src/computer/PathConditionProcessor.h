/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 juin 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef PATHCONDITIONPROCESSOR_H_
#define PATHCONDITIONPROCESSOR_H_

#include <computer/ExecutionEnvironment.h>

#include <fml/runtime/ExecutionData.h>


namespace sep
{


class BF;
class ExecutionEnvironment;

class PathConditionProcessor
{

public:

	////////////////////////////////////////////////////////////////////////////
	///// CHECK SATISFIABILITY
	////////////////////////////////////////////////////////////////////////////
	static bool isWeakSatisfiable(const BF & aCondition);

	////////////////////////////////////////////////////////////////////////////
	///// FIRED TIMED CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool setNodeCondition(ExecutionData & apED,
			const BF & theCondition);
	static bool addNodeCondition(ExecutionData & apED,
			const BF & theCondition);


	////////////////////////////////////////////////////////////////////////////
	///// FIRED TIMED CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool setNodeTimedCondition(ExecutionData & apED,
			const BF & theTimedCondition);
	static bool addNodeTimedCondition(ExecutionData & apED,
			const BF & theTimedCondition);


	////////////////////////////////////////////////////////////////////////////
	///// PATH CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool addPathCondition(ExecutionData & apED,
			const BF & theCondition, bool considerFiredConditon = true);


	static bool appendPathCondition(ExecutionData & apED, BF & theCondition,
			CollectionOfExecutionData & listOfOutputED);

	inline static bool appendPathCondition(ExecutionEnvironment & ENV,
			ExecutionData & apED, BF & theCondition)
	{
		return( appendPathCondition(apED, theCondition, ENV.outEDS) );
	}

	inline static bool appendPathCondition(ExecutionEnvironment & ENV)
	{
		return( appendPathCondition(ENV.inED, ENV.inFORM, ENV.outEDS) );
	}


	static bool setCondition(
			ExecutionData & apED, const BF & theNodeCondition,
			const BF & thePathCondition, bool considerFiredConditon = true);


	////////////////////////////////////////////////////////////////////////////////
	// PATH TIMED CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool addPathTimedCondition(ExecutionData & apED,
			const BF & theTimedCondition);

	inline static bool appendPathTimedCondition(ExecutionEnvironment & ENV,
			ExecutionData & apED, BF & theTimedCondition)
	{
		return( appendPathTimedCondition(apED,
				theTimedCondition, ENV.outEDS) );
	}

	static bool appendPathTimedCondition(ExecutionData & apED,
			BF & theTimedCondition,
			CollectionOfExecutionData & listOfOutputED);

	static bool setTimedCondition(ExecutionData & apED,
			const BF & theNodeTimedCondition,
			const BF & thePathTimedCondition);



public:
	/*
	 * ATTRIBUTE
	 */
	static bool CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED;

	static bool STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED;


	static bool PATH_CONDIDITON_DISJONCTION_SEPARATION_ENABLED;

	static bool NODE_CONDITION_COMPUTATION_ENABLED;


};


}

#endif /* PATHCONDITIONPROCESSOR_H_ */
