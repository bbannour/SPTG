/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEACTIVITYCOMPILER_H_
#define AVMCODEACTIVITYCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS_HEADER("ACTIVITY#STATEMENT",
		ActivityStatement, AbstractAvmcodeCompiler)

	BFCode compileStatementParams(
			COMPILE_CONTEXT * aCTX, const BFCode & aCode);
};


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("CONTEXT_SWITCHER",
		ContextSwitcherStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("IENABLE",
		IEnableStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("ENABLE",
		EnableStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("IDISABLE",
		IDisableStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("DISABLE",
		DisableStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("DISABLE#SELVES",
		DisableSelvesStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("IABORT",
		IAbortStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("ABORT",
		AbortStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("ABORT#SELVES",
		AbortSelvesStatement, AvmcodeActivityStatementCompiler)



AVMCODE_COMPILER_STATEMENT_CLASS("FORK",
		ForkStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_STATEMENT_CLASS("JOIN",
		JoinStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_CLASS("GOTO",
		GotoStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_CLASS("RTC",
		RtcStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("SCHEDULE",
		ScheduleStatement, AvmcodeActivityStatementCompiler)

AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS("SCHEDULE#IN",
		ScheduleInStatement, AvmcodeActivityStatementCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("INPUT_ENABLED",
		InputEnabledStatement, AbstractAvmcodeCompiler)



}

#endif /* AVMCODEACTIVITYCOMPILER_H_ */
