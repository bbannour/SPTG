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

#ifndef AVMCODEQUEUECOMPILER_H_
#define AVMCODEQUEUECOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_OPTIMIZER_CLASS(Push, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(AssignTop, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(Top, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(Pop, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(PopFrom, AbstractAvmcodeCompiler)



}

#endif /* AVMCODEQUEUECOMPILER_H_ */
