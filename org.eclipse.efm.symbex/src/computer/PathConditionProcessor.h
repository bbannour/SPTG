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

	static bool setNodeCondition(APExecutionData & apED,
			const BF & theCondition);
	static bool addNodeCondition(APExecutionData & apED,
			const BF & theCondition);


	////////////////////////////////////////////////////////////////////////////
	///// FIRED TIMED CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool setNodeTimedCondition(APExecutionData & apED,
			const BF & theTimedCondition);
	static bool addNodeTimedCondition(APExecutionData & apED,
			const BF & theTimedCondition);


	////////////////////////////////////////////////////////////////////////////
	///// PATH CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool addPathCondition(APExecutionData & apED,
			const BF & theCondition, bool considerFiredConditon = true);


	static bool appendPathCondition(APExecutionData & apED, BF & theCondition,
			CollectionOfAPExecutionData & listOfOutputED);

	inline static bool appendPathCondition(ExecutionEnvironment & ENV,
			APExecutionData & apED, BF & theCondition)
	{
		return( appendPathCondition(apED, theCondition, ENV.outEDS) );
	}

	inline static bool appendPathCondition(ExecutionEnvironment & ENV)
	{
		return( appendPathCondition(ENV.inED, ENV.inFORM, ENV.outEDS) );
	}


	static bool setCondition(
			APExecutionData & apED, const BF & theNodeCondition,
			const BF & thePathCondition, bool considerFiredConditon = true);


	////////////////////////////////////////////////////////////////////////////////
	// PATH TIMED CONDITION
	////////////////////////////////////////////////////////////////////////////

	static bool addPathTimedCondition(APExecutionData & apED,
			const BF & theTimedCondition);

	inline static bool appendPathTimedCondition(ExecutionEnvironment & ENV,
			APExecutionData & apED, BF & theTimedCondition)
	{
		return( appendPathTimedCondition(apED,
				theTimedCondition, ENV.outEDS) );
	}

	static bool appendPathTimedCondition(APExecutionData & apED,
			BF & theTimedCondition,
			CollectionOfAPExecutionData & listOfOutputED);

	static bool setTimedCondition(APExecutionData & apED,
			const BF & theNodeTimedCondition,
			const BF & thePathTimedCondition);



public:
	/*
	 * ATTRIBUTE
	 */
	static bool checkPathcondSat;
	static bool separationOfPcDisjunction;



};


}

#endif /* PATHCONDITIONPROCESSOR_H_ */
