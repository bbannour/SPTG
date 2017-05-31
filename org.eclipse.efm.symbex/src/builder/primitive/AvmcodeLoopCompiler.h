/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODELOOPCOMPILER_H_
#define AVMCODELOOPCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("LOOP#FOR", For, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("LOOP#FOREACH", Foreach, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("LOOP#WHILE_DO", WhileDo, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS("LOOP#DO_WHILE", DoWhile, AbstractAvmcodeCompiler)




} /* namespace sep */
#endif /* AVMCODELOOPCOMPILER_H_ */
