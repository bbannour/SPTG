/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILDER_COMPILER_BASEMACHINECOMPILER_H_
#define BUILDER_COMPILER_BASEMACHINECOMPILER_H_

#include <builder/compiler/BaseCompiler.h>


namespace sep
{


class AvmcodeCompiler;
class ExecutableForm;
class InstanceOfMachine;


class BaseMachineCompiler : public BaseCompiler
{


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BaseMachineCompiler(Configuration & aConfiguration,
			AvmcodeCompiler & anAvmcodeCompiler)
	: BaseCompiler( aConfiguration , anAvmcodeCompiler )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BaseMachineCompiler()
	{
		//!! NOTHING
	}


	/*
	 ***************************************************************************
	 * COMPILING EXECUTABLE - AVMPROGRAM
	 ***************************************************************************
	 */
	void postcompileExecutableSystem();

	void optimizeExecutable(ExecutableForm & anExecutableForm);

	void optimizeAllBehavioralRoutines(ExecutableForm & anExecutableForm);

	void optimizeInstance(ExecutableForm & anExecutableForm);

	void optimizeInstance(
			ExecutableForm & theExecutableContainer,
			InstanceOfMachine * anInstance);



	/**
	 * COMPILING EXECUTABLE SCHEDULER
	 */
	BFCode compileSchedulerRoutine(ExecutableForm & anExecutableForm,
			ListOfInstanceOfMachine & usedInstance, BFCode & aSchedulerCode);

	void compileSchedulerRoutine(ExecutableForm & anExecutableForm,
			ListOfInstanceOfMachine & usedInstance,
			BFCode & aSchedulerCode, BFCode & compilCode);

	BFCode compileSchedulerRoutine(
			ExecutableForm & anExecutableForm, BFCode & aCode);

	BFCode optimizeSchedulingRoutine(
			ExecutableForm & anExecutableForm, BFCode & aSchedulerCode);

};


} /* namespace sep */
#endif /* BUILDER_COMPILER_BASEMACHINECOMPILER_H_ */
