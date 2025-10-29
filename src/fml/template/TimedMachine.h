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

#include <fml/infrastructure/Variable.h>
#include <fml/lib/ITypeSpecifier.h>


namespace sep
{

class BF;
class BFCode;

class Machine;
class Specifier;


class TimedMachine
{

public:

	static Variable * SYSTEM_VAR_GLOBAL_TIME;
	static Variable * SYSTEM_VAR_DELTA_TIME;


	static avm_type_specifier_kind_t
	timeTypeSpecifierKind(const Specifier & specifier);


	static const TypeSpecifier & timeTypeSpecifier(const Specifier & specifier);

	static void genProperty(Machine & machine);

	static void genBehavior(Machine & machine);
	static void genBehaviorInit(Machine & machine);
	static void genBehaviorIRun(Machine & machine);

	static void genTimeUpdate(Machine & machine);

	static void updateClock(
			Machine & modelMachine, Machine & machine, const BF & varDeltaTime,
			const BFCode & seqCode, const std::string & aQualifiedNameID = "");


	static void updateClock(Machine & machine,
			const TableOfVariable & variables, const BF & varDeltaTime,
			const BFCode & seqCode, const std::string & aQualifiedNameID = "");
};

} /* namespace sep */

#endif /* TIMEDMACHINE_H_ */
