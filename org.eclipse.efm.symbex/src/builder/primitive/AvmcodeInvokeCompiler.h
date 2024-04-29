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

#ifndef AVMCODEINVOKECOMPILER_H_
#define AVMCODEINVOKECOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_OPTIMIZER_CLASS(InvokeNew, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_CLASS(InvokeRoutine, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_CLASS(
		"INVOKE#TRANSITION", InvokeTransition, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_CLASS(InvokeMethod, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(InvokeProgram, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(InvokeFunction, AbstractAvmcodeCompiler)


}

#endif /* AVMCODEINVOKECOMPILER_H_ */
