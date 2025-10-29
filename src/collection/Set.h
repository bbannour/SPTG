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
#ifndef CONTAINER_SET_H_
#define CONTAINER_SET_H_

#include <set>
#include <vector>

#include <common/Element.h>


namespace sep
{


template< typename T >
class Set final :  public std::set< T >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef       T &         reference;
	typedef const T &         const_reference;

	typedef std::set< T >     BaseSet;
	typedef std::vector< T >  BaseVector;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Set()
	: BaseSet()
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Set(const Set & aSet)
	: BaseSet( aSet )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Set()
	{
		BaseSet::clear();
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline bool empty() const
	{
		return( BaseSet::empty() );
	}

	inline bool nonempty() const
	{
		return( not BaseSet::empty() );
	}

	inline bool singleton() const
	{
		//return( size() == 1 );

		typename BaseSet::const_iterator it = BaseSet::begin();
		typename BaseSet::const_iterator itEnd = BaseSet::end();
		return( (it != itEnd) && ((++it) == itEnd) );
	}

	inline bool populated() const
	{
		//return( size() > 1 );

		typename BaseSet::const_iterator it = BaseSet::begin();
		typename BaseSet::const_iterator itEnd = BaseSet::end();
		return( (it != itEnd) && ((++it) != itEnd) );
	}


	/**
	 * contains a particular element
	 */
	inline bool contains(const T & arg) const
	{
		typename BaseSet::const_iterator it = BaseSet::begin();
		typename BaseSet::const_iterator itEnd = BaseSet::end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it) == arg )
			{
				return( true );
			}
		}

		return( false );
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * append
	 ***************************************************************************
	 */

	template< typename _TOE >
	inline void append(const std::set< _TOE > & aCollection)
	{
		BaseSet::insert(BaseSet::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void splice(const std::set< _TOE > & aCollection)
	{
		BaseSet::splice(BaseSet::end(),
				aCollection);
	}

	template< typename _TOE >
	inline void append(const std::vector< _TOE > & aCollection)
	{
		BaseSet::insert(BaseSet::end(),
				aCollection.begin(), aCollection.end());
	}

};


/**
 * MEMORY MANAGEMENT
 * DESTROY
 */

template< class T >
void destroy(Set< T * > * & aSet)
{
	while( aSet->nonempty() )
	{
		sep::destroy( aSet->pop_last() );
	}

	delete( aSet );

	aSet = nullptr;
}


template< class T >
void destroy(Set< T > * & aSet)
{
	while( aSet->nonempty() )
	{
		sep::destroy( aSet->pop_last() );
	}

	delete( aSet );

	aSet = nullptr;
}


}

#endif /*CONTAINER_SET_H_*/
