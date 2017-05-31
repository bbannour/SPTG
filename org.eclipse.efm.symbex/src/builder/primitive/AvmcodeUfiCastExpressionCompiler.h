/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 mai 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCODEUFICASTEXPRESSIONCOMPILER_H_
#define AVMCODEUFICASTEXPRESSIONCOMPILER_H_

#include <builder/primitive/AbstractAvmcodeCompiler.h>


namespace sep
{


class CompilationEnvironment;
class UniFormIdentifier;


AVMCODE_COMPILER_CLASS_HEADER(UfiExpression, AbstractAvmcodeCompiler)
public:
	BF compileUfiExpression(COMPILE_CONTEXT * aCTX,
			const UniFormIdentifier & theUFI);
};



}

#endif /* AVMCODEUFICASTEXPRESSIONCOMPILER_H_ */
