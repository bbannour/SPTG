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
#ifndef SEW_SYMBEX_CONTROLLER_H_
#define SEW_SYMBEX_CONTROLLER_H_

#include <sew/SymbexJob.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

class ExecutionContext;
class SymbexControllerRequestManager;
class SymbexControllerUnitManager;
class SymbexDispatcher;

class SymbexController : public SymbexJob
{

	AVM_DECLARE_UNCLONABLE_CLASS(SymbexController)


	/**
	 * ATTRIBUTES
	 */
	SymbexControllerRequestManager & mSymbexRequestManager;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	SymbexController(SymbexDispatcher & aSymbexDispatcher,
			WObject * wfParameterObject,
			SymbexControllerUnitManager & aControllerUnitManager);


	/**
	 * DESTRUCTOR
	 */
	virtual ~SymbexController()
	{
		//!! NOTHING
	}


	/**
	 * Thread main Run Method
	 */
	virtual void operator()();


	void analyseReady();

	void analyseResult();

	/**
	 * report Eval
	 */
	void reportEval() const;

};


} /* namespace sep */

#endif /*SEW_SYMBEX_CONTROLLER_H_*/
