/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEJUMPCOMPILER_H_
#define AVMCODEJUMPCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_STATEMENT_CLASS(
		"BREAK", Break, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_CLASS(
		"CONTNUE", Continue, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"RETURN", Return, AbstractAvmcodeCompiler)

AVMCODE_COMPILER_STATEMENT_OPTIMIZER_CLASS(
		"EXIT", Exit, AbstractAvmcodeCompiler)






} /* namespace sep */
#endif /* AVMCODEJUMPCOMPILER_H_ */
