/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACEMANAGER_H_
#define TRACEMANAGER_H_

#include "TraceNormalizer.h"

#include <collection/List.h>

#include <fml/trace/TraceSequence.h>


namespace sep
{

class TraceFormatter;


class TraceManager  :  public APList< TraceSequence * >
{

public:
	/**
	 * ATTRIBUTES
	 */
	avm_size_t nextTID;

	TraceNormalizer normalizer;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceManager()
	: APList< TraceSequence * >( ),
	nextTID( 0 ),

	normalizer( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceManager()
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	avm_size_t currentTID() const
	{
		return( nextTID );
	}

	avm_size_t newTID()
	{
		return( ++nextTID );
	}

	void resetTID()
	{
		nextTID = 0;
	}


	////////////////////////////////////////////////////////////////////////////
	// REDUCING API
	////////////////////////////////////////////////////////////////////////////

	inline void reduce(TraceSequence * aTraceElt)
	{
		normalizer.reduce(aTraceElt);
		if( aTraceElt->points.nonempty() )
		{
		}
	}

	inline void normalize()
	{
		normalizer.normalize(this);
	}

	void resetTraceID()
	{
		normalizer.resetTraceID(this);
	}

	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////
	virtual void toStream(OutStream & os) const;

};


} /* namespace sep */

#endif /* TRACEMANAGER_H_ */
