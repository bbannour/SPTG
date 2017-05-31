/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILDER_COMPILER_COMPILEROFPROGRAM_H_
#define BUILDER_COMPILER_COMPILEROFPROGRAM_H_

#include <builder/compiler/BaseCompiler.h>


namespace sep
{


class AvmcodeCompiler;
class CompilerOfAvmCode;
class Compiler;
class CompilerOfVariable;

class AvmCode;
class AvmProgram;
class ExecutableForm;
class ObjectElement;



class CompilerOfProgram  :  public BaseCompiler
{

protected:
	/**
	 * ATTRIBUTE
	 */
	CompilerOfVariable & mDataCompiler;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompilerOfProgram(Compiler & aCompiler);


	/**
	 * DESTRUCTOR
	 */
	virtual ~CompilerOfProgram()
	{
		//!! NOTHING
	}


	/**
	 ***************************************************************************
	 * PRECOMPILATION
	 ***************************************************************************
	 */
	void precompileProgram(ExecutableForm * aContainer, ObjectElement * aProgram);


	/**
	 ***************************************************************************
	 * COMPILATION
	 ***************************************************************************
	 */
	void compileProgram(AvmProgram * anAvmProgram);

};


}



#endif /* BUILDER_COMPILER_COMPILEROFPROGRAM_H_ */
