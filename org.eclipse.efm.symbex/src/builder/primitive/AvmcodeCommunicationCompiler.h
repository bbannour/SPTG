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

#ifndef AVMCODECOMMUNICATIONCOMPILER_H_
#define AVMCODECOMMUNICATIONCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"INPUT", Input, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"INPUT#FROM", InputFrom, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"INPUT#SAVE", InputSave, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"INPUT#VAR", InputVar, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"INPUT#ENV", InputEnv, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"OUTPUT", Output, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"OUTPUT#TO", OutputTo, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"OUTPUT#VAR", OutputVar, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"OUTPUT#ENV", OutputEnv, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(AbsentPresent, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(Obs, AbstractAvmcodeCompiler)


}

#endif /* AVMCODECOMMUNICATIONCOMPILER_H_ */
