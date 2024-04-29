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
#ifndef CONTAINER_COLLECTION_H_
#define CONTAINER_COLLECTION_H_

#include <list>
#include <vector>

namespace sep
{


template< typename T >
class Collection
{

public:

	/**
	 * TYPEDEF
	 * iterator
	 * reference
	 */
	typedef T       &  reference;
	typedef const T &  const_reference;


	/**
	 * DESTRUCTOR
	 */
	virtual ~Collection()
	{
		//!! NOTHING
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * push back & front
	 ***************************************************************************
	 */
	virtual void push_back(const T & arg) = 0;

	virtual void push_back(const std::list< T > & aCollection) = 0;

	virtual void push_back(const std::vector< T > & aCollection) = 0;


	virtual void push_front(const T & arg) = 0;

	virtual void push_front(const std::list< T > & aCollection) = 0;

	virtual void push_front(const std::vector< T > & aCollection) = 0;



	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	virtual bool empty() const = 0;

	virtual bool nonempty() const = 0;

	virtual bool singleton() const = 0;

	virtual bool populated() const = 0;


//	virtual std::size_t size() const = 0;


	/**
	 * contains a particular element
	 */
	virtual bool contains(const T & arg) const = 0;

	virtual bool contains(const T * arg) const = 0;


	/*
	 ***************************************************************************
	 * SETTER
	 * append
	 ***************************************************************************
	 */
	virtual void append(const T & arg) = 0;

	inline virtual void append(const T & arg1, const T & arg2)
	{
		append(arg1);
		append(arg2);
	}

	inline virtual void append(const T & arg1, const T & arg2, const T & arg3)
	{
		append(arg1);
		append(arg2);
		append(arg3);
	}

	inline void append(const T & arg1,
			const T & arg2, const T & arg3, const T & arg4)
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

	inline virtual void append(T * anArrayOfArgument, int anArgSize)
	{
		for (int i = 0 ; i < anArgSize ; ++i)
		{
			append(anArrayOfArgument[i]);
		}
	}


	inline void append(const std::vector< T > & aCollection)
	{
		typename std::vector< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			append( (*it) );
		}
	}

	inline void append(const std::list< T > & aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			append( (*it) );
		}
	}



	/*
	 ***************************************************************************
	 * GETTER - SETTER
	 * add_unique
	 ***************************************************************************
	 */
	virtual void add_unique(const T & arg) = 0;

//	virtual void add_unique(T * arg) = 0;

//	virtual void add_unique(const T & arg1, const T & arg2) = 0;

	inline virtual void add_unique(const T & arg1, const T & arg2)
	{
		add_unique(arg1);
		add_unique(arg2);
	}


	inline virtual void add_unique(const std::list< T > & aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			add_unique( (*it) );
		}
	}

//	template< typename _TOE >
//	inline void add_unique(const std::list< _TOE > & aCollection)
//	{
//		typename std::list< T >::const_iterator it = aCollection.begin();
//		for( ; it != aCollection.end() ; ++it )
//		{
//			add_unique( (*it) );
//		}
//	}

	inline virtual void add_unique(const std::vector< T > & aCollection)
	{
		typename std::vector< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			add_unique( (*it) );
		}
	}

	inline virtual void add_unique(const T * anArrayOfArgument, int anArgSize)
	{
		for (int i = 0 ; i < anArgSize ; ++i)
		{
			add_unique( anArrayOfArgument[i] );
		}
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * first & ... & last
	 ***************************************************************************
	 */
	virtual reference first() = 0;
	virtual const_reference first() const = 0;

	virtual T pop_first() = 0;

	virtual void pop_first_to(T & theFirst) = 0;

	virtual reference second() = 0;
	virtual const_reference second() const = 0;

	virtual reference last() = 0;
	virtual const_reference last() const = 0;

	virtual T pop_last() = 0;

	virtual void pop_last_to(T & theLast) = 0;


	/*
	 ***************************************************************************
	 * SETTER
	 * reset
	 ***************************************************************************
	 */
	virtual void reset() = 0;

//	inline virtual void reset(const T & arg)
//	{
//		reset();
//
//		append(arg);
//	}
//
//	inline void reset(const T & arg1, const T & arg2)
//	{
//		reset();
//
//		append(arg1);
//		append(arg2);
//	}
//
//	inline void reset(const T & arg1, const T & arg2, const T & arg3)
//	{
//		reset();
//
//		append(arg1);
//		append(arg2);
//		append(arg3);
//	}
//
//	inline void reset(const T & arg1,
//			const T & arg2, const T & arg3, const T & arg4)
//	{
//		reset();
//
//		append(arg1);
//		append(arg2);
//		append(arg3);
//		append(arg4);
//	}
//
//	inline void reset(const T & arg1, const T & arg2,
//			const T & arg3, const T & arg4, const T & arg5)
//	{
//		reset();
//
//		append(arg1);
//		append(arg2);
//		append(arg3);
//		append(arg4);
//		append(arg5);
//	}
//
//
//	inline void reset(T* anArrayOfArgument, int anArgSize)
//	{
//		reset();
//
//		for (int i = 0 ; i < anArgSize ; ++i)
//		{
//			push_back(anArrayOfArgument[i]);
//		}
//	}
//
//
//	inline virtual void reset(const std::list< T > & aCollection)
//	{
//		reset();
//
//		push_back(aCollection);
//	}
//
//	inline virtual void reset(const std::vector< T > & aCollection)
//	{
//		reset();
//
//		push_back(aCollection);
//	}
//
//
//	template< typename _TOE >
//	inline void reset(const std::list< _TOE > & aCollection)
//	{
//		reset();
//
//		push_back(aCollection);
//	}
//
//	template< typename _TOE >
//	inline void reset(const std::vector< _TOE > & aCollection)
//	{
//		reset();
//
//		push_back(aCollection);
//	}


	/*
	 ***************************************************************************
	 * SETTER
	 * remove
	 ***************************************************************************
	 */
	virtual void remove(const T & arg) = 0;

	inline void remove(const std::vector< T > & aCollection)
	{
		typename std::vector< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			remove( (*it) );
		}
	}

	inline void remove(const std::list< T > & aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			remove( (*it) );
		}
	}


//	virtual void makeUnique() = 0;

};


}

#endif /*CONTAINER_COLLECTION_H_*/

