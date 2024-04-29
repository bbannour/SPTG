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

#ifndef BUILDER_COMPILER_COMPILEROFVARIABLE_H_
#define BUILDER_COMPILER_COMPILEROFVARIABLE_H_

#include <builder/compiler/BaseCompiler.h>

#include <collection/Vector.h>

#include <fml/type/TypeSpecifier.h>


namespace sep
{


class AvmProgram;
class ExecutableForm;

class InstanceOfData;

class Variable;

class Compiler;



class CompilerOfVariable  :  public BaseCompiler
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompilerOfVariable(Compiler & aCompiler);


	/**
	 * DESTRUCTOR
	 */
	virtual ~CompilerOfVariable()
	{
		//!! NOTHING
	}


	/**
	 ***************************************************************************
	 * PRECOMPILATION
	 ***************************************************************************
	 */

	void addPrecompileVariable(AvmProgram & aContainer, Symbol & aVariable,
			TableOfInstanceOfData & tableOfVariable,
			bool collectVarEnabled = false);

	static std::size_t nextOffset(TableOfInstanceOfData & tableOfVariable);


	void precompileTypeSpecifier(AvmProgram & aContainer, const BF & aDataType);

	void precompileVariable(AvmProgram & aContainer,
			const Variable & aVariable, TableOfInstanceOfData & tableOfVariable);

	BF precompileVariable_initialValue(AvmProgram & aContainer,
			const BaseTypeSpecifier & aTypeSpecifier, const BF & aValue);

	void precompileVariable_initialValue(AvmProgram & aContainer,
			InstanceOfData & aVarInstance);

	/**
	 ***************************************************************************
	 * COMPILATION
	 ***************************************************************************
	 */
	void compileVariable(ExecutableForm & anExecutable);

	void compileVariableOnCreate(ExecutableForm & anExecutable,
			TableOfInstanceOfData::ref_iterator itVar, BFCode & onInitialize);



	void compileVariable(AvmProgram & aProgram);

	void compileConstVariable(
			AvmProgram & aContainer, InstanceOfData & aVarInstance);

	void compileVariable(
			AvmProgram & aContainer, InstanceOfData & aVarInstance);

	void compileVariable_initialValue(
			AvmProgram & aContainer, InstanceOfData & aVarInstance);

	void compileTypeConstraint(
			AvmProgram & aContainer, InstanceOfData & aVarInstance);

};

}

#endif /* BUILDER_COMPILER_COMPILEROFVARIABLE_H_ */
