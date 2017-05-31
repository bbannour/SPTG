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

#ifndef AVMCODECONTAINERCOMPILER_H_
#define AVMCODECONTAINERCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_OPTIMIZER_CLASS(UnaryContainerStatement, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(UnaryWriteContainerStatement, AbstractAvmcodeCompiler)


AVMCODE_COMPILER_OPTIMIZER_CLASS(BinaryContainerStatement, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_OPTIMIZER_CLASS(BinaryWriteContainerStatement, AbstractAvmcodeCompiler)


}

#endif /* AVMCODECONTAINERCOMPILER_H_ */
