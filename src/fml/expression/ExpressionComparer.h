/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 déc. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXPRESSIONCOMPARER_H_
#define EXPRESSIONCOMPARER_H_

#include <common/BF.h>


namespace sep
{

class ArrayBF;
class BFCode;
class UniFormIdentifier;


class ExpressionComparer
{

public:

	/**
	 * USUAL COMPARISON
	 */
	static int compare(const BF & frst, const BF & snd);


	/**
	 * USUAL EQUALITY
	 */
	static bool isEQ(const BF & frst, const BF & snd);


	inline static bool isNEQ(const BF & frst, const BF & snd)
	{
		return( ! ExpressionComparer::isEQ(frst, snd) );
	}


	/**
	 * TRIVIAL EQUALITY
	 */
	inline static bool isTEQ(const BF & frst, const BF & snd)
	{
		return( frst.raw_pointer() == snd.raw_pointer() );
	}

	inline static bool isNTEQ(const BF & frst, const BF & snd)
	{
		return( frst.raw_pointer() != snd.raw_pointer() );
	}

};


}

#endif /* EXPRESSIONCOMPARER_H_ */
