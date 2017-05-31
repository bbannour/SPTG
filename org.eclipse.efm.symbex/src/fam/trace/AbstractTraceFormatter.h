/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef ABSTRACTTRACEFORMATTER_H_
#define ABSTRACTTRACEFORMATTER_H_

#include <printer/OutStream.h>


namespace sep
{

class AvmTraceGenerator;

class TraceManager;

class WObject;


class AbstractTraceFormatter
{

protected:
	/**
	 * ATTRIBUTES
	 */
	AvmTraceGenerator & mTraceGenerator;

	WrapData mWrapData;

	SymbexValueCSS mMultiValueArrayCSS;
	SymbexValueCSS mMultiValueParamsCSS;
	SymbexValueCSS mMultiValueStructCSS;

	// Lifelines
	bool mPrintLifelines;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractTraceFormatter(AvmTraceGenerator & aTraceGenerator)
	: mTraceGenerator( aTraceGenerator ),
	mWrapData( DEFAULT_WRAP_DATA.LINE_WIDTH, 0,
			DEFAULT_WRAP_DATA.TAB_WIDTH, "\n" ),

	mMultiValueArrayCSS ( DEFAULT_SYMBEX_VALUE_ARRAY_CSS  ),
	mMultiValueParamsCSS( DEFAULT_SYMBEX_VALUE_PARAMS_CSS ),
	mMultiValueStructCSS( DEFAULT_SYMBEX_VALUE_STRUCT_CSS ),

	// Lifelines
	mPrintLifelines( true )

	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AbstractTraceFormatter()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	virtual bool configure(WObject * wfParameterObject);

	virtual bool configureImpl(WObject * wfParameterObject) = 0;


	////////////////////////////////////////////////////////////////////////////
	// NUMERIZE API
	////////////////////////////////////////////////////////////////////////////

	virtual void format(TraceManager & aTraceManager) = 0;

};


} /* namespace sep */

#endif /* ABSTRACTTRACEFORMATTER_H_ */
