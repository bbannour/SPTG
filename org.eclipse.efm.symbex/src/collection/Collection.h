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


//	virtual avm_size_t size() const = 0;


	/**
	 * contains a particular element
	 */
	virtual bool contains(const T & arg) const = 0;


	/*
	 ***************************************************************************
	 * SETTER
	 * append
	 ***************************************************************************
	 */
	virtual void append(const T & arg) = 0;

	virtual void append(const T & arg1, const T & arg2) = 0;

	virtual void append(T * anArrayOfArgument, int anArgSize) = 0;


	/*
	 ***************************************************************************
	 * GETTER - SETTER
	 * add_union
	 ***************************************************************************
	 */
	virtual void add_union(const T & arg) = 0;

	virtual void add_union(const T & arg1, const T & arg2) = 0;


	virtual void add_union(const std::list< T > & aCollection) = 0;

	virtual void add_union(const std::vector< T > & aCollection) = 0;


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
	virtual void reset(const T & arg) = 0;

	virtual void reset(const std::list< T > & aCollection) = 0;

	virtual void reset(const std::vector< T > & aCollection) = 0;



//	virtual void makeUnique() = 0;

};


}

#endif /*CONTAINER_COLLECTION_H_*/

