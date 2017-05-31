/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TIMEDMACHINE_H_
#define TIMEDMACHINE_H_

#include <util/avm_string.h>

#include <fml/infrastructure/Variable.h>


namespace sep
{

class BF;
class BFCode;

class Machine;


class TimedMachine
{

public:

	static std::string VAR_ID_GLOBAL_TIME;
	static std::string VAR_ID_DELTA_TIME;

	static std::string ROUTINE_ID_TIME_GET;
	static std::string ROUTINE_ID_DELTA_GET;

	static std::string ROUTINE_ID_TIME_RESET;

	static std::string ROUTINE_ID_CLOCK_RESET;
	static std::string ROUTINE_ID_CLOCK_UPDATE;

	static Variable * SYSTEM_VAR_GLOBAL_TIME;
	static Variable * SYSTEM_VAR_DELTA_TIME;

	static void genProperty(Machine * machine);

	static void genBehavior(Machine * machine);
	static void genBehaviorInit(Machine * machine);
	static void genBehaviorIRun(Machine * machine);

	static void updateClock(const Machine * modelMachine, Machine * machine,
			const BF & varDeltaTime, const BFCode & seqCode,
			const std::string & aQualifiedNameID = "");


	static void updateClock(Machine * machine,
			const TableOfVariable & variables, const BF & varDeltaTime,
			const BFCode & seqCode, const std::string & aQualifiedNameID = "");
};

} /* namespace sep */

#endif /* TIMEDMACHINE_H_ */
