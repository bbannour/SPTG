/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 16 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TRACENORMALIZER_H_
#define TRACENORMALIZER_H_


namespace sep
{

class TraceManager;
class TraceSequence;


class TraceNormalizer
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceNormalizer()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceNormalizer()
	{
		//!! NOTHING
	}


	////////////////////////////////////////////////////////////////////////////
	// REDUCING API
	////////////////////////////////////////////////////////////////////////////

	void reduce(TraceSequence & aTraceElt);

	void normalize(TraceManager & aTraceManager);

	void resetTraceID(TraceManager & aTraceManager);

};


} /* namespace sep */

#endif /* TRACENORMALIZER_H_ */
