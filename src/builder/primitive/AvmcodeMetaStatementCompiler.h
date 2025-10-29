/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 mars 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEMETASTATEMENTCOMPILER_H_
#define AVMCODEMETASTATEMENTCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_OPTIMIZER_CLASS(Nothing, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(InformalExpression, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(TraceExpression, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(DebugExpression, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(CommentExpression, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_CLASS(MetaEvalStatement, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(MetaRunStatement, AbstractAvmcodeCompiler)



} /* namespace sep */
#endif /* AVMCODEMETASTATEMENTCOMPILER_H_ */
