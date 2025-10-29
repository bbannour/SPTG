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

#ifndef WORKFLOW_WORKFLOW_H_
#define WORKFLOW_WORKFLOW_H_

#include <common/RunnableElement.h>


namespace sep
{

class SymbexEngine;
class WObject;


class Workflow final :  public RunnableElement
{

	AVM_DECLARE_UNCLONABLE_CLASS(Workflow)

protected:
	/**
	* ATTRIBUTES
	*/
	SymbexEngine * mMainSymbexEngine;
	SymbexEngine * mCurrentSymbexEngine;

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Workflow(const WObject * wfParameterObject = nullptr)
	: RunnableElement( wfParameterObject ),

	mMainSymbexEngine( nullptr ),
	mCurrentSymbexEngine( nullptr )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Workflow()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mMainSymbexEngine
	 */
	inline SymbexEngine * getMainSymbexEngine()
	{
		return mMainSymbexEngine;
	}

	/**
	 * LOADER - DISPOSER
	 */
	bool load();

	void dispose();


	/**
	 * Configure
	 */
	virtual bool configure() override
	{
		return true;
	}

	bool configure(const WorkflowParameter & aWorkflowParameter);


	////////////////////////////////////////////////////////////////////////////
	// START / STOP / KILL / SUSPEND / RESUME  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool start();


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool initImpl() override
	{
		return( true );
	}

	virtual bool exitImpl() override;



	/**
	 * REPORT TRACE
	 */
	virtual void report(OutStream & os) const override;


	/*
	 * PROCESSING
	 */
	bool startComputing();


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	void toStream(OutStream & os) const override;

};

} /* namespace sep */

#endif /* WORKFLOW_WORKFLOW_H_ */
