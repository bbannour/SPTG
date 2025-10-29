/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 20 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEGUARDCOMPILER_H_
#define AVMCODEGUARDCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS_HEADER(
		"GUARD", Guard, AbstractAvmcodeCompiler)
protected:
	BFCodeList trivialAssignmentsSequence;

public:
	static bool MAKE_TRIVIAL_ASSIGMENT_FROM_GUARD_ENABLED;
};


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS_HEADER(
		"TIMED_GUARD", TimedGuard, AbstractAvmcodeCompiler)
protected:
	BFCodeList trivialAssignmentsSequence;

public:
	static bool MAKE_TRIVIAL_ASSIGMENT_FROM_TIMED_GUARD_ENABLED;
};


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"EVENT", Event, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"CHECKSAT", Checksat, AbstractAvmcodeCompiler)


}

#endif /* AVMCODEGUARDCOMPILER_H_ */
