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

#include <collection/Collection.h>

#include <common/Element.h>


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

	inline void pop_back()
	{
		BaseList::pop_back();
	}

	inline void pop_back(std::size_t count)
	{
		for( ; (count > 0) && nonempty() ; --count )
		{
			BaseList::pop_back();
		}
	}


	inline virtual void push_back(const T & arg) override final
	{
		BaseList::push_back(arg);
	}


	inline virtual void push_back(const std::list< T > & aCollection) override
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


	inline virtual void push_back(const std::vector< T > & aCollection) override
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


	inline virtual void push_front(const T & arg) override
	{
		BaseList::push_front(arg);
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * pop | push  front
	 ***************************************************************************
	 */

	inline void pop_front()
	{
		BaseList::pop_front();
	}

	inline void pop_front(std::size_t count)
	{
		for( ; (count > 0) && nonempty() ; --count )
		{
			BaseList::pop_front();
		}
	}


	inline virtual void push_front(const std::list< T > & aCollection) override
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


	inline virtual void push_front(
			const std::vector< T > & aCollection) override
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
	inline virtual bool empty() const override final
	{
		return( BaseList::empty() );
	}

	inline virtual bool nonempty() const override final
	{
		return( not BaseList::empty() );
	}

	inline virtual bool singleton() const override final
	{
		return( BaseList::size() == 1 );

//		typename BaseList::const_iterator it = BaseList::begin();
//		typename BaseList::const_iterator itEnd = BaseList::end();
//		return( (it != itEnd) && ((++it) == itEnd) );
	}

	inline virtual bool populated() const override final
	{
		return( BaseList::size() > 1 );

//		typename BaseList::const_iterator it = BaseList::begin();
//		typename BaseList::const_iterator itEnd = BaseList::end();
//		return( (it != itEnd) && ((++it) != itEnd) );
	}


	//	inline virtual std::size_t size() const override
	//	{
	//		return( BaseList::size() );
	//	}


	/**
	 * contains a particular element
	 */
	inline virtual bool contains(const T & arg) const override final
	{
		for( const auto & it : (*this) )
		{
			if( it == arg )
			{
				return( true );
			}
		}

		return( false );
	}

	inline virtual bool contains(const T * arg) const override
	{
		for( const auto & it : (*this) )
		{
			if( it == *arg )
			{
				return( true );
			}
		}

		return( false );
	}


	/**
	 * has an intersection with another list
	 */
	inline bool intersect(const std::list< T > & aCollection) const
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
	inline virtual void append(const T & arg) override final
	{
		BaseList::push_back(arg);
	}

	template< typename _TOE >
	inline void append(const std::list< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void append(const std::vector< _TOE > & aCollection)
	{
		BaseList::insert(BaseList::end(),
				aCollection.begin(), aCollection.end());
	}

	using Collection<T>::append;


	/*
	 ***************************************************************************
	 * SETTER
	 * splice
	 ***************************************************************************
	 */
	template< typename _TOE >
	inline void splice(std::list< _TOE > & aCollection)
	{
		BaseList::splice(BaseList::end(), aCollection);
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * add_unique
	 ***************************************************************************
	 */
	inline virtual void add_unique(const T & arg) override
	{
		if( not contains(arg) )
		{
			BaseList::push_back(arg);
		}
	}

	using Collection<T>::add_unique;


	/*
	 ***************************************************************************
	 * GETTER
	 * first & ... & last
	 ***************************************************************************
	 */
	inline virtual reference first() override final
	{
		return( BaseList::front() );
	}

	inline virtual const_reference first() const override
	{
		return( BaseList::front() );
	}


	inline virtual T pop_first() override final
	{
		T theFirst = BaseList::front();

		BaseList::pop_front();

		return( theFirst );
	}

	inline virtual void pop_first_to(T & theFirst) override
	{
		theFirst = BaseList::front();

		BaseList::pop_front();
	}

	inline void remove_first()
	{
		BaseList::pop_front();
	}


	inline virtual reference second() override
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( populated() )
				<< "Expected a List with size() > 1 !!!"
				<< SEND_EXIT;

		return( *( ++(BaseList::begin()) ) );
	}

	inline virtual const_reference second() const override
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( populated() )
				<< "Expected a List with size() > 1 !!!"
				<< SEND_EXIT;

		return( *( ++(BaseList::begin()) ) );
	}


	inline virtual reference last() override
	{
		return( *( BaseList::rbegin() ) );
	}

	inline virtual const_reference last() const override
	{
		return( *( BaseList::rbegin() ) );
	}


	inline virtual T pop_last() override
	{
		T theLast = BaseList::back();

		BaseList::pop_back();

		return( theLast );
	}

	inline virtual void pop_last_to(T & theLast) override
	{
		theLast = BaseList::back();

		BaseList::pop_back();
	}

	inline void remove_last()
	{
		BaseList::pop_back();
	}


	inline reference at(std::size_t index)
	{
		typename BaseList::iterator it = BaseList::begin();
		typename BaseList::iterator itEnd = BaseList::end();
		for( ; (index > 0) && (it != itEnd) ; ++it , --index )
		{
			//!!! NOTHING
		}

		return( ((index == 0) && (it != itEnd)) ? *it : last() );
	}

	inline const_reference at(std::size_t index) const
	{
		typename BaseList::const_iterator it = BaseList::begin();
		typename BaseList::const_iterator itEnd = BaseList::end();
		for( ; (index > 0) && (it != itEnd) ; ++it , --index )
		{
			//!!! NOTHING
		}

		return( ((index == 0) && (it != itEnd)) ? *it : last() );
	}


	inline reference get(std::size_t index)
	{
		return( at(index) );
	}

	inline const_reference get(std::size_t index) const
	{
		return( at(index) );
	}


	inline T pop_index(std::size_t index)
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
	 * remove
	 * makeUnique
	 ***************************************************************************
	 */
	inline virtual void reset() override
	{
		BaseList::clear();
	}

	using Collection<T>::reset;


	inline virtual void remove(const T & arg) override
	{
		BaseList::remove(arg);
	}

	using Collection<T>::remove;


	inline void makeUnique()
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

	aList = nullptr;
}

template< class T >
void destroy(List< T * > & aList)
{
	while( aList.nonempty() )
	{
		sep::destroy( aList.pop_last() );
	}
}


template< class T >
void destroy(List< T > * aList)
{
	delete( aList );

	aList = nullptr;
}



}

#endif /*CONTAINER_LIST_H_*/
