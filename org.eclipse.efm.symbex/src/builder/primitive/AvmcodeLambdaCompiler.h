/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODELAMBDACOMPILER_H_
#define AVMCODELAMBDACOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_CLASS(LambdaApply, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(LambdaLet, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_CLASS(LambdaExpr, AbstractAvmcodeCompiler)


}

#endif /* AVMCODELAMBDACOMPILER_H_ */
