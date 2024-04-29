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

#include <fml/runtime/ExecutionContext.h>

#include <cstddef>

namespace sep
{

class AvmTraceGenerator;

class WObject;

class TraceManager;


class AbstractTraceBuilder
{

public:
	/**
	 * CONSTANTS
	 * DEFAULT PROFILE
	 */
	static const std::size_t DEFAULT_TRACE_COUNT_LIMIT = 42;

protected:
	/**
	 * ATTRIBUTE
	 */
	AvmTraceGenerator & mProcessor;

	bool mDataSelectionModifiedFlags;

	std::size_t pathCount;
	std::size_t pathCountLimit;

	bool oneTracePerfile;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AbstractTraceBuilder(AvmTraceGenerator & aProcessor)
	: mProcessor( aProcessor ),
	mDataSelectionModifiedFlags( false ),

	pathCount( 0 ),
	pathCountLimit( DEFAULT_TRACE_COUNT_LIMIT ),
	oneTracePerfile( false )
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


	/**
	 * GETTER
	 * pathCount
	 * pathCountLimit
	 */
	inline std::size_t getPathCount() const
	{
		return pathCount;
	}

	inline std::size_t getPathCountLimit() const
	{
		return pathCountLimit;
	}

	/**
	 * TESTER
	 * oneTracePerfile
	 */
	inline bool isOneTracePerfile() const
	{
		return oneTracePerfile;
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////

	bool configure(const WObject * wfParameterObject);

	virtual bool configureImpl(const WObject * wfParameterObject) = 0;


	////////////////////////////////////////////////////////////////////////////
	// CONSTRUCTION API
	////////////////////////////////////////////////////////////////////////////

	virtual void build(TraceManager & aTraceManager,
			const ListOfExecutionContext & rootECs) = 0;

};


} /* namespace sep */

#endif /* ABSTRACTTRACEBUILDER_H_ */
