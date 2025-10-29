/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef BUILDER_COMPILER_COMPILER_H_
#define BUILDER_COMPILER_COMPILER_H_

#include <builder/compiler/BaseMachineCompiler.h>

#include <builder/compiler/CompilerOfInteraction.h>
#include <builder/compiler/CompilerOfTransition.h>
#include <builder/compiler/CompilerOfVariable.h>


namespace sep
{

class Configuration;

class AvmcodeCompiler;

class AvmProgram;
class ExecutableForm;
class ExecutableSystem;
class InstanceOfBuffer;
class InstanceOfMachine;
class Machine;
class PropertyPart;
class System;


class Compiler : public BaseMachineCompiler
{

protected:
	/**
	 * ATTRIBUTE
	 */
	CompilerOfVariable mVariableCompiler;

	CompilerOfTransition mTransitionCompiler;

	CompilerOfInteraction mComCompiler;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Compiler(Configuration & aConfiguration, AvmcodeCompiler & anAvmcodeCompiler);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Compiler()
	{
		//!! NOTHING
	}

	/**
	 * GETTER
	 */

	inline CompilerOfVariable & getVariableCompiler()
	{
		return( mVariableCompiler );
	}


	/**
	 * CONFIGURE
	 */
	bool configure();


	/**
	 * METHODS
	 * start
	 */
	virtual bool start(System & aSystem);

	// Due to [-Woverloaded-virtual=]
	using BaseMachineCompiler::start;

	/*
	 ***************************************************************************
	 * PRE-COMPILING SYSTEM - [STATE]MACHINE - TRANSITION
	 ***************************************************************************
	 */
	void precompilePropertyPart(
			ExecutableForm & anExecutable, const PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);

	void precompileDataType(
			AvmProgram & aProgram, const PropertyPart & theDeclaration,
			TableOfInstanceOfData & tableOfVariable);


	void precompileExecutableCompositePart(
			ExecutableForm & aContainer, Machine & anExecutableSpec);

	void precompileExecutable(
			ExecutableForm & aContainer, Machine & anExecutableSpec);

	ExecutableForm * precompileExecutableModel(
			ExecutableForm & aContainer, Machine & anExecutableSpec);

	void precompileExecutablePrototype(
			ExecutableForm & aContainer, Machine & anExecutableSpec);

	void precompileExecutableInstanceStatic(
			ExecutableForm & aContainer, const Machine & anExecutableSpec);

	void precompileExecutableInstanceDynamique(
			ExecutableForm & aContainer, const Machine & anExecutableSpec);

	void precompileExecutableGroup(
			ExecutableForm & aContainer, const Machine & aStatemachine);


	void precompileSystem(System & aSystem);


	/**
	 * setInheritedSpecifier from container to owned elements
	 */
	void setInheritedSpecifier(
			ExecutableForm & aContainer, ExecutableForm & anExecutable);

	void setInheritedSpecifier(
			ExecutableForm & aContainer, InstanceOfMachine & aMachine);


	/*
	 ***************************************************************************
	 * COMPILING EXECUTABLE - PROGRAM
	 ***************************************************************************
	 */
	void compileExecutableSystem();

	void compileExecutable(ExecutableForm & anExecutable);

	void compilePrograms(ExecutableForm & anExecutable);

	void compileProgram(AvmProgram & aProgram);


	/*
	 ***************************************************************************
	 * COMPILING SYSTEM - [STATE]MACHINE - TRANSITION
	 ***************************************************************************
	 */
	void compileAllInstances(ExecutableForm & anExecutableForm);

	void compileInstance(
			ExecutableForm & theExecutableContainer,
			InstanceOfMachine * anInstanceMachine);

	void compileInstanceParameters(
			ExecutableForm & theExecutableContainer,
			InstanceOfMachine * anInstanceMachine);

	void compileBaseMachine(ExecutableForm & anExecutableForm);

	void compileProcedure(ExecutableForm & anExecutableForm);

	void compileMachine(ExecutableForm & anExecutableForm);

	void compileSystem(ExecutableForm & anExecutableForm);
	void compileStatemachine(ExecutableForm & anExecutableForm);

	void compileExecutableMocCompositeStructure(
			ExecutableForm & anExecutableForm);

	void compileExecutableMocStateTransitionStructure(
			ExecutableForm & anExecutableForm);

	void compileStatemachineBasic(ExecutableForm & anExecutableForm);
	void compileStatemachinePseudo(ExecutableForm & anExecutableForm);
	void compileStatemachineHistory(ExecutableForm & anExecutableForm);
	void compilePseudostateEnding(ExecutableForm & anExecutableForm);


	void removeSubmachineInputEnabledCode(const ExecutableForm & anExecutableForm);

	void computeInputEnabledCom(ExecutableForm & anExecutableForm);

	void computeInputEnabledBuffer(ExecutableForm & anExecutableForm);

	void compileAllBehavioralRoutines(ExecutableForm & theExecutable);

	void compileBehaviorInitialization(ExecutableForm & theExecutable);
	void compileBehaviorEnabling(ExecutableForm & theExecutable);
	void compileBehaviorDisabling(ExecutableForm & theExecutable);
	void compileBehaviorAborting(ExecutableForm & theExecutable);

	void compileBehaviorScheduling(ExecutableForm & theExecutable);
	void setRdvScheduling(ExecutableForm & theExecutable);

};



}

#endif /*BUILDER_COMPILER_COMPILER_H_*/
