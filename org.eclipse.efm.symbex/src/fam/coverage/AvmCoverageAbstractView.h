/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 19 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMCOVERAGEABSTRACTVIEW_H_
#define AVMCOVERAGEABSTRACTVIEW_H_

#include <common/RunnableElement.h>
#include <fam/coverage/AvmCoverageHeuristicProperty.h>

#include <collection/Typedef.h>

#include <fml/runtime/ExecutionContext.h>


namespace sep
{

class AvmCoverageProcessor;
class OutStream;

class AvmCoverageStatistics;

class ExecutionContext;


class AvmCoverageAbstractView  :
		public RunnableElement,
		public IHeuristicContextWeight
{

	/**
	 * ATTRIBUTES
	 */
protected:
	AvmCoverageProcessor & mCoverageProcessor;

	AvmCoverageStatistics & mCoverageStatistics;

	AvmCoverageHeuristicProperty & mHeuristicProperty;

	// Computing drive variable
	ListOfExecutionContext::iterator itQueue;
	ListOfExecutionContext::iterator endQueue;

	ExecutionContext::child_iterator itEC;
	ExecutionContext::child_iterator endEC;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageAbstractView(
			AvmCoverageProcessor & aCoverageProcessor, WObject * wfParameterObject);

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageAbstractView()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// COVERAGE PROCESSOR API
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool configure()
	{
		// INITIALIZATION
		mConfigFlag = RunnableElement::configure();

		// standard processor/view user configuration
		mConfigFlag = configureImpl() && mConfigFlag;

		return( mConfigFlag );
	}

	virtual bool configureImpl() = 0;


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool initImpl()
	{
		//!! NOTHING
		return true;
	}

	virtual bool exitImpl()
	{
		//!! NOTHING
		return true;
	}


	////////////////////////////////////////////////////////////////////////////
//	// REPORT API
//	////////////////////////////////////////////////////////////////////////////
//	virtual void reportDefault(OutStream & os) const;
//
//
//	////////////////////////////////////////////////////////////////////////////
//	// PROCESSOR PROCESSING API
//	////////////////////////////////////////////////////////////////////////////
//	virtual bool preprocessing();
//
//	virtual bool postprocessing();
//
//
//	////////////////////////////////////////////////////////////////////////////
//	// PROCESSOR FILTERING API
//	////////////////////////////////////////////////////////////////////////////
//	virtual bool prefiltering(ListOfExecutionContext & ecQueue);
//
//	virtual bool postfiltering(ListOfExecutionContext & ecQueue);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const
	{
		//!! NOTHING
	}

};

} /* namespace sep */

#endif /* AVMCOVERAGEABSTRACTVIEW_H_ */
