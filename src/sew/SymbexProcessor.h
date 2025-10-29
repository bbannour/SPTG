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
#ifndef SEW_SYMBEX_PROCESSOR_H_
#define SEW_SYMBEX_PROCESSOR_H_



#include <sew/SymbexJob.h>



namespace sep
{


class AvmPrimitiveProcessor;
class ExecutionContext;
class SymbexControllerUnitManager;
class SymbexDispatcher;


class SymbexProcessor  :  public SymbexJob
{

	AVM_DECLARE_UNCLONABLE_CLASS(SymbexProcessor)


protected:
	/**
	 * ATTRIBUTES
	 */
	AvmPrimitiveProcessor & mPrimitiveProcessor;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexProcessor(SymbexDispatcher & aSymbexDispatcher,
			const WObject * wfParameterObject,
			SymbexControllerUnitManager & aControllerUnitManager);


	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexProcessor()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure() override;


	/**
	 * Thread main Run Method
	 */
	virtual void operator()() override;


	/**
	 * Execution step
	 */
	void initStep();
	void initStep(ExecutionContext & anEC);

	void runStep();
	void runStep(ExecutionContext & anEC);
	void runStep(ExecutionContext & anEC, const BF & aRunnableElement);


	/**
	 * EVAL TRACE
	 */
	void traceBoundEval();

	void tracePreEval(const ExecutionContext & anEC);

	void tracePostEval(const ExecutionContext & anEC);

};


} /* namespace sep */

#endif /*SEW_SYMBEX_PROCESSOR_H_*/
