/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 1 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODELOOKUPEXPRCOMPILER_H_
#define AVMCODELOOKUPEXPRCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


AVMCODE_COMPILER_EXPRESSION_OPTIMIZER_CLASS(
		"LOOKUP", LookupExpression, AbstractAvmcodeCompiler)



}

#endif /* AVMCODELOOKUPEXPRCOMPILER_H_ */
