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
#ifndef CONTAINER_PAIR_H_
#define CONTAINER_PAIR_H_

#include <common/Element.h>


namespace sep
{


template< typename T , typename U >
class Pair final
{

public:
	/**
	 * TYPEDEF
	 */
	typedef       T & referenceT;
	typedef const T & const_referenceT;

	typedef       U & referenceU;
	typedef const U & const_referenceU;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Pair()
	: theFirst( ),
	theSecond( )
	{
	}

	explicit Pair(T one)
	: theFirst( one ),
	theSecond( )
	{
	}

//	explicit Pair(U two)
//	: theFirst( ),
//	theSecond( two )
//	{
//	}

	explicit Pair(T one, U two)
	: theFirst( one ),
	theSecond( two )
	{
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Pair(const Pair & aPair)
	: theFirst( aPair.theFirst ),
	theSecond( aPair.theSecond )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Pair()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * theFirst
	 */
	referenceT first()
	{
		return( theFirst );
	}

	const_referenceT first() const
	{
		return( theFirst );
	}

	void setFirst(referenceT first)
	{
		theFirst = first;
	}


	/**
	 * GETTER - SETTER
	 * theSecond
	 */
	referenceU second()
	{
		return( theSecond );
	}

	const_referenceU second() const
	{
		return( theSecond );
	}

	void setSecond(referenceU second)
	{
		theSecond = second;
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */
	inline bool operator==(const Pair & other) const
	{
		return( (theFirst == other.theFirst) && (theSecond == other.theSecond) );
	}

	inline bool operator!=(const Pair & other) const
	{
		return( (theFirst != other.theFirst) || (theSecond != other.theSecond) );
	}

protected:
	/*
	 * ATTRIBUTES
	 */
	T theFirst;

	U theSecond;


};



/**
 * MEMORY MANAGEMENT
 * DESTROY
 */

template< typename T , typename U >
void destroy(Pair< T *  , U * > * aPair)
{
	sep::destroy( aPair->first() );
	sep::destroy( aPair->second() );

	delete( aPair );

	aPair = nullptr;
}


template< typename T , typename U >
void destroy(Pair< T *  , U > * aPair)
{
	sep::destroy( aPair->first() );

	delete( aPair );

	aPair = nullptr;
}


template< typename T , typename U >
void destroy(Pair< T , U * > * aPair)
{
	sep::destroy( aPair->second() );

	delete( aPair );

	aPair = nullptr;
}


template< typename T , typename U >
void destroy(Pair< T , U > * aPair)
{
	delete( aPair );

	aPair = nullptr;
}




}

#endif /*CONTAINER_PAIR_H_*/
