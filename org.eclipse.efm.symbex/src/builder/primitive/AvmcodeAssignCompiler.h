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

#ifndef AVMCODEASSIGNCOMPILER_H_
#define AVMCODEASSIGNCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_OPTIMIZER_CLASS(Assign, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(AssignAfter, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_NO_OPTIMIZER_CLASS("ASSIGN#OP", AssignOp, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_NO_OPTIMIZER_CLASS("ASSIGN#OP#AFTER", AssignOpAfter, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(AssignRef, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(AssignMacro, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(AssignUnary, AbstractAvmcodeCompiler)


}

#endif /* AVMCODEASSIGNCOMPILER_H_ */
