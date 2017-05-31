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

#ifndef ABSTRACTTRACEBUILDER_H_
#define ABSTRACTTRACEBUILDER_H_

namespace sep
{

class AvmTraceGenerator;

class WObject;

class TraceManager;


class AbstractTraceBuilder
{

protected:
	/**
	 * ATTRIBUTE
	 */
	AvmTraceGenerator & mProcessor;

	bool mDataSelectionModifiedFlags;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractTraceBuilder(AvmTraceGenerator & aProcessor)
	: mProcessor( aProcessor ),
	mDataSelectionModifiedFlags( false )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~AbstractTraceBuilder()
	{
		//!! NOTHING
	}



	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(WObject * wfParameterObject);

	virtual bool configureImpl(WObject * wfParameterObject) = 0;


	////////////////////////////////////////////////////////////////////////////
	// CONSTRUCTION API
	////////////////////////////////////////////////////////////////////////////

	virtual void build(TraceManager & aTraceManager) = 0;

};


} /* namespace sep */

#endif /* ABSTRACTTRACEBUILDER_H_ */
