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

#ifndef AVMCOVERAGETRACEVIEW_H_
#define AVMCOVERAGETRACEVIEW_H_

#include <fam/coverage/AvmCoverageAbstractView.h>


namespace sep
{

class AvmCoverageProcessor;
class OutStream;
class ExecutionContext;


class AvmCoverageTraceView  :  public AvmCoverageAbstractView
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmCoverageTraceView(
			AvmCoverageProcessor & aCoverageProcessor, WObject * wfParameterObject)
	: AvmCoverageAbstractView( aCoverageProcessor , wfParameterObject )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmCoverageTraceView()
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

	virtual bool configureImpl();


	////////////////////////////////////////////////////////////////////////////
	// REPORT API
	////////////////////////////////////////////////////////////////////////////
	virtual void reportDefault(OutStream & os) const;


	////////////////////////////////////////////////////////////////////////////
	// PROCESS API
	////////////////////////////////////////////////////////////////////////////
	virtual bool preprocess();

	virtual bool postprocess();


	////////////////////////////////////////////////////////////////////////////
	// FILTER API
	////////////////////////////////////////////////////////////////////////////
	virtual bool prefilter();
	virtual bool prefilter(ExecutionContext & anEC);

	virtual bool postfilter();
	virtual bool postfilter(ExecutionContext & anEC);


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const
	{
		//!! NOTHING
	}

};

} /* namespace sep */

#endif /* AVMCOVERAGETRACEVIEW_H_ */
