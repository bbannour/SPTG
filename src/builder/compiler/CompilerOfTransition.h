/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILDER_COMPILER_COMPILEROFTRANSITION_H_
#define BUILDER_COMPILER_COMPILEROFTRANSITION_H_

#include <builder/compiler/BaseCompiler.h>

#include <collection/Typedef.h>

#include <fml/executable/AvmTransition.h>
#include <fml/operator/OperatorManager.h>

#include <fml/infrastructure/TransitionMoc.h>



namespace sep
{


class AvmcodeCompiler;
class CompilerOfAvmCode;
class Compiler;
class CompilerOfVariable;

class AvmCode;
class AvmTransition;
class ExecutableForm;
class Machine;
class Transition;
class WObject;


class CompilerOfTransition  :  public BaseCompiler
{

protected:
	/**
	 * ATTRIBUTE
	 */
	Compiler & mCompiler;

	CompilerOfVariable & mVariableCompiler;


	// MOC:> Model of Compilation
	List< TransitionMoc * >  mMocStack;

	TransitionMoc * mCurrentMoc;

	TransitionMoc mDefaultMoc;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	CompilerOfTransition(Compiler & aCompiler);

	/**
	 * DESTRUCTOR
	 */
	virtual ~CompilerOfTransition()
	{
		//!! NOTHING
	}


	void setDefaultMoc();


	void pushMoc(const WObject * mocTransition);

	void popMoc();


	/**
	 ***************************************************************************
	 * PRECOMPILATION
	 ***************************************************************************
	 */
	void precompileTransition(
			ExecutableForm & aContainer, Transition & aTransition);


	/**
	 ***************************************************************************
	 * COMPILATION
	 ***************************************************************************
	 */
	void compileTransition(AvmTransition & anAvmTransition);

	BFCode scheduleListOfTransition(
			ExecutableForm & anExecutableForm, const BFList & listOfTransition);

	BFCode scheduleListOfTransition(ExecutableForm & anExecutableForm,
		const BFList & listOfTransition, const BFList & listOfElseTransition);

	Machine * getTransitionTarget(
			const Transition & aTransition, const BF & smTarget);

	BF compileTransitionTarget(
			AvmTransition & anAvmTransition, const BF & smTarget);

	void compileStatemachineTransition(ExecutableForm & anExecutableForm,
			const BFCode & runRoutine);

	void compileStateForkOutputTransition(ExecutableForm & anExecutableForm,
			const BFCode & runRoutine);

	void compileStateJoinInputTransition(ExecutableForm & anExecutableForm);

};

}

#endif /* BUILDER_COMPILER_COMPILEROFTRANSITION_H_ */
