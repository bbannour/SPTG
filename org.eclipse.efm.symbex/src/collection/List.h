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
#ifndef CONTAINER_LIST_H_
#define CONTAINER_LIST_H_

#include <list>

#include <util/avm_assert.h>
#include <util/avm_numeric.h>
#include <base/SmartPointerUtil.h>

#include <collection/Collection.h>


namespace sep
{


template< typename T >
class List :
		public std::list< T >,
		public Collection< T >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef       T &         reference;
	typedef const T &         const_reference;

	typedef std::list< T >    BaseList;
	typedef std::vector< T >  BaseVector;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	List()
	: BaseList()
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	List(const List & aList)
	: BaseList( aList )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	explicit List(const T & arg)
	: BaseList()
	{
		append(arg);
	}

	explicit List(const T & arg1, const T & arg2)
	: BaseList()
	{
		append(arg1, arg2);
	}

	explicit List(T arg1, T arg2, T arg3)
	: BaseList()
	{
		append(arg1, arg2, arg3);
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~List()
	{
		BaseList::clear();
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * pop | push  back
	 ***************************************************************************
	 */

	inline virtual void pop_back()
	{
		BaseList::pop_back();
	}

	inline void pop_back(avm_size_t count)
	{
		for( ; (count > 0) && nonempty() ; --count )
		{
			BaseList::pop_back();
		}
	}


	inline virtual void push_back(const T & arg)
	{
		BaseList::push_back(arg);
	}


	inline virtual void push_back(const std::list< T > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_back(const std::list< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}


	inline virtual void push_back(const std::vector< T > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_back(const std::vector< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}


	inline virtual void push_front(const T & arg)
	{
		BaseList::push_front(arg);
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * pop | push  front
	 ***************************************************************************
	 */

	inline virtual void pop_front()
	{
		BaseList::pop_front();
	}

	inline void pop_front(avm_size_t count)
	{
		for( ; (count > 0) && nonempty() ; --count )
		{
			BaseList::pop_front();
		}
	}


	inline virtual void push_front(const std::list< T > & aCollection)
	{
		BaseList::insert(BaseList::begin(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_front(const std::list< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::begin(),
				aCollection.begin(), aCollection.end());
	}


	inline virtual void push_front(const std::vector< T > & aCollection)
	{
		BaseList::insert(BaseList::begin(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_front(const std::vector< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::begin(),
				aCollection.begin(), aCollection.end());
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const
	{
		return( BaseList::empty() );
	}

	inline virtual bool nonempty() const
	{
		return( not BaseList::empty() );
	}

	inline virtual bool singleton() const
	{
		//return( size() == 1 );

		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		return( (it != itEnd) && ((++it) == itEnd) );
	}

	inline virtual bool populated() const
	{
		//return( size() > 1 );

		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		return( (it != itEnd) && ((++it) != itEnd) );
	}


	//	inline virtual avm_size_t size() const
	//	{
	//		return( BaseList::size() );
	//	}


	/**
	 * contains a particular element
	 */
	inline virtual bool contains(const T & arg) const
	{
		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it) == arg )
			{
				return( true );
			}
		}

		return( false );
	}


	/**
	 * has an intersection with another list
	 */
	inline virtual bool intersect(const std::list< T > & aCollection) const
	{
		typename std::list< T >::const_iterator itCol;
		typename std::list< T >::const_iterator endItCol = aCollection.end();

		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		for( ; it != itEnd ; ++it )
		{
			for( itCol = aCollection.begin() ; itCol != endItCol ; ++itCol )
			{
				if( (*it) == (*itCol) )
				{
					return( true );
				}
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
	inline virtual void append(const T & arg)
	{
		BaseList::push_back(arg);
	}

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


	inline virtual void append(T * anArrayOfArgument, int anArgSize)
	{
		for (int i = 0 ; i < anArgSize ; ++i)
		{
			push_back(anArrayOfArgument[i]);
		}
	}

	template< typename _TOE >
	inline void append(const std::list< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void splice(std::list< _TOE > & aCollection)
	{
		BaseList::splice(BaseList::end(), aCollection);
	}

	template< typename _TOE >
	inline void append(const std::vector< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * add_union
	 ***************************************************************************
	 */
	inline virtual void add_union(const T & arg)
	{
		if( not contains(arg) )
		{
			BaseList::push_back(arg);
		}
	}

	inline virtual void add_union(const T & arg1, const T & arg2)
	{
		add_union(arg1);
		add_union(arg2);
	}


	inline virtual void add_union(T * anArrayOfArgument, int anArgSize)
	{
		for (int i = 0 ; i < anArgSize ; ++i)
		{
			add_union( anArrayOfArgument[i] );
		}
	}


	inline virtual void add_union(const std::list< T > & aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			add_union( (*it) );
		}
	}

	inline virtual void add_union(const std::list< T > * aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection->begin();
		for( ; it != aCollection->end() ; ++it )
		{
			add_union( (*it) );
		}
	}

	inline virtual void add_union(const std::vector< T > & aCollection)
	{
		typename std::vector< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			add_union( (*it) );
		}
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * first & ... & last
	 ***************************************************************************
	 */
	inline virtual reference first()
	{
		return( BaseList::front() );
	}

	inline virtual const_reference first() const
	{
		return( BaseList::front() );
	}


	inline virtual T pop_first()
	{
		T theFirst = BaseList::front();

		BaseList::pop_front();

		return( theFirst );
	}

	inline virtual void pop_first_to(T & theFirst)
	{
		theFirst = BaseList::front();

		BaseList::pop_front();
	}

	inline void remove_first()
	{
		BaseList::pop_front();
	}


	inline virtual reference second()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( populated() )
				<< "Expected a List with size() > 1 !!!"
				<< SEND_EXIT;

		return( *( ++(BaseList::begin()) ) );
	}

	inline virtual const_reference second() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( populated() )
				<< "Expected a List with size() > 1 !!!"
				<< SEND_EXIT;

		return( *( ++(BaseList::begin()) ) );
	}


	inline virtual reference last()
	{
		return( *( BaseList::rbegin() ) );
	}

	inline virtual const_reference last() const
	{
		return( *( BaseList::rbegin() ) );
	}


	inline virtual T pop_last()
	{
		T theLast = BaseList::back();

		BaseList::pop_back();

		return( theLast );
	}

	inline virtual void pop_last_to(T & theLast)
	{
		theLast = BaseList::back();

		BaseList::pop_back();
	}

	inline void remove_last()
	{
		BaseList::pop_back();
	}


	inline virtual reference at(avm_size_t index)
	{
		typename BaseList::iterator it = BaseList::begin();
		typename BaseList::iterator itEnd = BaseList::end();
		for( ; (index > 0) && (it != itEnd) ; ++it , --index )
		{
			//!!! NOTHING
		}

		return( ((index == 0) && (it != itEnd)) ? *it : last() );
	}

	inline virtual const_reference at(avm_size_t index) const
	{
		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		for( ; (index > 0) && (it != itEnd) ; ++it , --index )
		{
			//!!! NOTHING
		}

		return( ((index == 0) && (it != itEnd)) ? *it : last() );
	}


	inline virtual reference get(avm_size_t index)
	{
		return( at(index) );
	}

	inline virtual const_reference get(avm_size_t index) const
	{
		return( at(index) );
	}


	inline T pop_index(avm_size_t index)
	{
		typename BaseList::iterator it = BaseList::begin();
		typename BaseList::iterator itEnd = BaseList::end();
		for( ; (index > 0) && (it != itEnd) ; ++it , --index )
		{
			//!!! NOTHING
		}

		if( (index == 0) && (it != itEnd) )
		{
			T theElt = *it;

			BaseList::erase( it );

			return( theElt );
		}
		else
		{
			return( pop_last() );
		}
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * reset
	 ***************************************************************************
	 */
	inline virtual void reset(const T & arg)
	{
		BaseList::clear();
		push_back(arg);
	}


	inline virtual void reset(const std::list< T > & aCollection)
	{
		BaseList::clear();

		push_back(aCollection);
	}

	inline virtual void reset(const std::vector< T > & aCollection)
	{
		BaseList::clear();

		push_back(aCollection);
	}


	template< typename _TOE >
	inline void reset(const std::list< _TOE > & aCollection)
	{
		BaseList::clear();

		push_back(aCollection);
	}

	template< typename _TOE >
	inline void reset(const std::vector< _TOE > & aCollection)
	{
		BaseList::clear();

		push_back(aCollection);
	}


	inline virtual void remove(const T & arg)
	{
		BaseList::remove(arg);
	}

	inline void remove(const std::list< T > & aCollection)
	{
		typename std::list< T >::const_iterator it = aCollection.begin();
		for( ; it != aCollection.end() ; ++it )
		{
			BaseList::remove( (*it) );
		}
	}


	inline virtual void makeUnique()
	{
		if( populated() )
		{
			typename BaseList::const_iterator itTmp;

			typename BaseList::iterator it = BaseList::begin();
			for( ++it ; it != BaseList::end() ; )
			{
				for( itTmp = BaseList::begin() ; itTmp != it ; ++itTmp )
				{
					if( (*itTmp) == (*it) )
					{
						break;
					}
				}

				if( itTmp != it )
				{
					it = BaseList::erase(it);
				}
				else
				{
					++it;
				}
			}
		}

		//		BaseList::sort();
		//		BaseList::unique();
	}

};



template< typename T >
class APList : public List< T >
{
public:
	/**
	 * TYPEDEF
	 */
	typedef T       & reference;
	typedef const T & const_reference;

	typedef List< T >  BaseAPList;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	APList()
	: BaseAPList()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	APList(const APList & aList)
	: BaseAPList( )
	{
		typename BaseAPList::const_iterator it = aList.begin();
		typename BaseAPList::const_iterator itEnd = aList.end();
		for( ; it != itEnd ; ++it )
		{
			BaseAPList::push_back( sep::incrReferenceCount( *it ) );
		}
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~APList()
	{
		clear();
	}

	/**
	 * CLEAR
	 */
	void clear()
	{
		while( BaseAPList::nonempty() )
		{
			sep::destroy( BaseAPList::pop_last() );
		}

		BaseAPList::clear();
	}

};



/**
 * MEMORY MANAGEMENT
 * DESTROY
 */

template< class T >
void destroy(List< T * > * aList)
{
	while( aList->nonempty() )
	{
		sep::destroy( aList->pop_last() );
	}

	delete( aList );

	aList = NULL;
}


template< class T >
void destroy(List< T > * aList)
{
	delete( aList );

	aList = NULL;
}



}

#endif /*CONTAINER_LIST_H_*/
