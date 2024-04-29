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
#ifndef CONTAINER_MULTISET_H_
#define CONTAINER_MULTISET_H_

#include <set>

#include <collection/Collection.h>

#include <common/Element.h>

namespace sep
{


template< typename T >
class Multiset  :  public std::multiset< T >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef       T &         reference;
	typedef const T &         const_reference;

	typedef std::multiset< T >  BaseMultiset;
	typedef std::vector< T >    BaseVector;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Multiset()
	: BaseMultiset()
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Multiset(const Multiset & aMultiset)
	: BaseMultiset( aMultiset )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	explicit Multiset(const T & arg)
	: BaseMultiset()
	{
		append(arg);
	}

	explicit Multiset(const T & arg1, const T & arg2)
	: BaseMultiset()
	{
		append(arg1, arg2);
	}

	explicit Multiset(const T & arg1, const T & arg2, const T & arg3)
	: BaseMultiset()
	{
		append(arg1, arg2, arg3);
	}

	explicit Multiset(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4)
	: BaseMultiset()
	{
		append(arg1, arg2, arg3, arg4);
	}

	explicit Multiset(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4, const T & arg5)
	: BaseMultiset()
	{
		append(arg1, arg2, arg3, arg4, arg5);
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Multiset()
	{
		BaseMultiset::clear();
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline bool empty() const
	{
		return( BaseMultiset::empty() );
	}

	inline bool nonempty() const
	{
		return( not BaseMultiset::empty() );
	}

	inline bool singleton() const
	{
		typename
		BaseMultiset::const_iterator it = BaseMultiset::begin();
		typename
		BaseMultiset::const_iterator itEnd = BaseMultiset::end();
		return( (it != itEnd) && ((++it) == itEnd) );
	}

	inline bool populated() const
	{
		typename
		BaseMultiset::const_iterator it = BaseMultiset::begin();
		typename
		BaseMultiset::const_iterator itEnd = BaseMultiset::end();
		return( (it != itEnd) && ((++it) != itEnd) );
	}


	//	inline virtual std::size_t size() const override
	//	{
	//		return( BaseMultiset::size() );
	//	}


	/**
	 * contains a particular element
	 */
	inline bool contains(const T & arg) const
	{
		typename BaseMultiset::const_iterator it = BaseMultiset::begin();
		typename BaseMultiset::const_iterator itEnd = BaseMultiset::end();
		for( const auto & it : (*this) )
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
	inline void append(const T & arg)
	{
		BaseMultiset::push_back(arg);
	}

	inline virtual void append(const T & arg1, const T & arg2)
	{
		append(arg1);
		append(arg2);
	}

	inline void append(const T & arg1, const T & arg2, const T & arg3)
	{
		append(arg1);
		append(arg2);
		append(arg3);
	}

	inline void append(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4)
	{
		append(arg1);
		append(arg2);
		append(arg3);
		append(arg4);
	}

	inline void append(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4, const T & arg5)
	{
		append(arg1);
		append(arg2);
		append(arg3);
		append(arg4);
		append(arg5);
	}


	template< typename _TOE >
	inline void append(const std::multiset< _TOE > & aCollection)
	{
		BaseMultiset::insert(BaseMultiset::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void splice(const std::multiset< _TOE > & aCollection)
	{
		BaseMultiset::splice(
				BaseMultiset::end(), aCollection);
	}

	template< typename _TOE >
	inline void append(const std::vector< _TOE > & aCollection)
	{
		BaseMultiset::insert(BaseMultiset::end(),
				aCollection.begin(), aCollection.end());
	}

};


/**
 * MEMORY MANAGEMENT
 * DESTROY
 */

template< class T >
void destroy(Multiset< T * > * & aMultiset)
{
	while( aMultiset->nonempty() )
	{
		sep::destroy( aMultiset->pop_last() );
	}

	delete( aMultiset );

	aMultiset = nullptr;
}


template< class T >
void destroy(Multiset< T > * & aMultiset)
{
	while( aMultiset->nonempty() )
	{
		sep::destroy( aMultiset->pop_last() );
	}

	delete( aMultiset );

	aMultiset = nullptr;
}


}

#endif /*CONTAINER_MULTISET_H_*/
