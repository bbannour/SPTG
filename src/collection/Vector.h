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
#ifndef CONTAINER_VECTOR_H_
#define CONTAINER_VECTOR_H_

#include <vector>

#include <util/avm_assert.h>
#include <util/avm_numeric.h>

#include <collection/Collection.h>

#include <common/Element.h>


namespace sep
{


template<typename T>
class Vector :
		public std::vector< T >,
		public Collection< T >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef T       &         reference;
	typedef const T &         const_reference;

	typedef std::list< T >    BaseList;
	typedef std::vector< T >  BaseVector;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Vector()
	: BaseVector()
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	Vector(const Vector & aVec)
	: BaseVector( aVec )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Others
	 */
	explicit Vector(std::size_t count)
	: BaseVector(count)
	{
		//!! NOTHING
	}

	explicit Vector(std::size_t count, const T & elem)
	: BaseVector(count, elem)
	{
		//!! NOTHING
	}

	explicit Vector(const T & arg)
	: BaseVector()
	{
		append(arg);
	}

	explicit Vector(const T & arg1, const T & arg2)
	: BaseVector()
	{
		append(arg1, arg2);
	}

	explicit Vector(const T & arg1, const T & arg2, const T & arg3)
	: BaseVector()
	{
		append(arg1, arg2, arg3);
	}

	explicit Vector(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4)
	: BaseVector()
	{
		append(arg1, arg2, arg3, arg4);
	}

	explicit Vector(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4, const T & arg5)
	: BaseVector()
	{
		append(arg1, arg2, arg3, arg4, arg5);
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Vector()
	{
		BaseVector::clear();
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * push back & front
	 ***************************************************************************
	 */
	inline virtual void push_back(const T & arg) override
	{
		BaseVector::push_back(arg);
	}


	inline virtual void push_back(const std::list< T > & aCollection) override
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_back(const std::list< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}


	inline virtual void push_back(const std::vector< T > & aCollection) override
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_back(const std::vector< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}



	inline virtual void push_front(const T & arg) override
	{
		BaseVector::insert(BaseVector::begin(), arg);
	}

	inline virtual void push_front(const std::list< T > & aCollection) override
	{
		BaseVector::insert(BaseVector::begin(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_front(const std::list< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::begin(),
				aCollection.begin(), aCollection.end());
	}


	inline virtual void push_front(
			const std::vector< T > & aCollection) override
	{
		BaseVector::insert(BaseVector::begin(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void push_front(const std::vector< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::begin(),
				aCollection.begin(), aCollection.end());
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const override
	{
		return( BaseVector::empty() );
	}

	inline virtual bool nonempty() const override
	{
		return( not BaseVector::empty() );
	}

	inline virtual bool singleton() const override
	{
		return( BaseVector::size() == 1 );
	}

	inline virtual bool populated() const override
	{
		return( BaseVector::size() > 1 );
	}


	/**
	 * contains a particular element
	 */
	inline virtual bool contains(const T & arg) const override
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


	inline bool contains(const std::vector< T > & aCollection)
	{
		typename std::vector< T >::const_iterator it = aCollection.begin();
		typename std::vector< T >::const_iterator itEnd = aCollection.end();
		for( ; it != itEnd ; ++it )
		{
			if( not contains( (*it) ) )
			{
				return( false );
			}
		}

		if(empty() && !aCollection.empty())
		{
			return( false );
		}
		else
		{
			return( true );
		}
	}


	/**
	 * find index of  a particular element
	 */
	template< typename U >
	inline int find(U arg) const
	{
		for( std::size_t it = 0 ; it != BaseVector::size() ; ++it )
		{
			if( BaseVector::at(it) == arg )
			{
				return( it );
			}
		}


		return( -1 );
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * append
	 ***************************************************************************
	 */
	inline virtual void append(const T & arg) override
	{
		BaseVector::push_back(arg);
	}


	template< typename _TOE >
	inline void append(const std::list< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}

	template< typename _TOE >
	inline void append(const std::vector< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
	}

	using Collection<T>::append;


	/*
	 ***************************************************************************
	 * SETTER
	 * appendTail
	 * splice
	 ***************************************************************************
	 */
	template< typename _TOE >
	inline void appendTail(const std::vector< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin() + 1, aCollection.end());
	}

	template< typename _TOE >
	inline void splice(std::vector< _TOE > & aCollection)
	{
		BaseVector::insert(BaseVector::end(),
				aCollection.begin(), aCollection.end());
		aCollection.clear();
	}


	/*
	 ***************************************************************************
	 * SETTER
	 * add_unique
	 ***************************************************************************
	 */
	inline virtual void add_unique(const T & arg) override final
	{
		if( not contains(arg) )
		{
			BaseVector::push_back(arg);
		}
	}

	using Collection<T>::add_unique;


//	inline virtual void add_unique(T * arg) override
//	{
//		if( not contains(arg) )
//		{
//			BaseVector::push_back(*arg);
//		}
//	}
//
//
//	inline virtual void add_unique(const std::list< T > & aCollection) override
//	{
//		typename std::list< T >::const_iterator it = aCollection.begin();
//		for( ; it != aCollection.end() ; ++it )
//		{
//			add_unique( (*it) );
//		}
//	}
//
//	inline virtual void add_unique(const std::vector< T > & aCollection) override
//	{
//		typename std::vector< T >::const_iterator it = aCollection.begin();
//		for( ; it != aCollection.end() ; ++it )
//		{
//			add_unique( (*it) );
//		}
//	}


	/*
	 ***************************************************************************
	 * GETTER
	 * first & ... & last
	 ***************************************************************************
	 */
	inline virtual reference first() override
	{
		return( BaseVector::front() );
	}

	inline virtual const_reference first() const override
	{
		return( BaseVector::front() );
	}

	inline reference getArg1()
	{
		return  get(0);
	}

	inline const_reference getArg1() const
	{
		return  get(0);
	}


	inline void pop_front()
	{
		BaseVector::erase(BaseVector::begin());
	}


	inline virtual T pop_first() override
	{
		T theFirst = BaseVector::front();

		BaseVector::erase( BaseVector::begin() );

		return( theFirst );
	}

	inline virtual void pop_first_to(T & theFirst) override
	{
		theFirst = BaseVector::front();

		BaseVector::erase( BaseVector::begin() );
	}

	inline void remove_first()
	{
		BaseVector::erase( BaseVector::begin() );
	}


	inline virtual reference second() override
	{
		return( get(1) );
	}

	inline virtual const_reference second() const override
	{
		return( get(1) );
	}

	inline reference getArg2()
	{
		return  get(1);
	}

	inline const_reference getArg2() const
	{
		return  get(1);
	}


	inline reference third()
	{
		return( get(2) );
	}

	inline const_reference third() const
	{
		return( get(2) );
	}

	inline reference getArg3()
	{
		return  get(2);
	}

	inline const_reference getArg3() const
	{
		return  get(2);
	}


	inline reference fourth()
	{
		return( get(3) );
	}

	inline const_reference fourth() const
	{
		return( get(3) );
	}

	inline reference getArg4()
	{
		return  get(3);
	}

	inline const_reference getArg4() const
	{
		return  get(3);
	}


	inline reference fifth()
	{
		return( get(4) );
	}

	inline const_reference fifth() const
	{
		return( get(4) );
	}

	inline reference getArg5()
	{
		return  get(4);
	}

	inline const_reference getArg5() const
	{
		return  get(4);
	}


	inline reference sixth()
	{
		return( get(5) );
	}

	inline const_reference sixth() const
	{
		return( get(5) );
	}

	inline reference getArg6()
	{
		return  get(5);
	}

	inline const_reference getArg6() const
	{
		return  get(5);
	}


	inline reference seventh()
	{
		return  get(6);
	}

	inline const_reference seventh() const
	{
		return  get(6);
	}

	inline reference getArg7()
	{
		return  get(6);
	}

	inline const_reference getArg7() const
	{
		return  get(6);
	}


	inline virtual reference last() override
	{
		return( BaseVector::back() );
	}

	inline virtual const_reference last() const override
	{
		return( BaseVector::back() );
	}


	inline virtual T pop_last() override
	{
		T theLast = BaseVector::back();

		BaseVector::pop_back();

		return( theLast );
	}

	inline virtual void pop_last_to(T & theLast) override
	{
		theLast = BaseVector::back();

		BaseVector::pop_back();
	}

	inline void remove_last()
	{
		BaseVector::pop_back();
	}

	inline reference get(std::size_t index)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::at(index) );
	}

	inline const_reference get(std::size_t index) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::at(index) );
	}

////////////////////////////////////////////////////////////////////////////////
//////// UNCOMMENT FOR << vector::_M_range_check >> EXCEPTION DEBUGGING ////////
////////////////////////////////////////////////////////////////////////////////
//
//	inline reference at(std::size_t index)
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::at(index) );
//	}
//
//	inline const_reference at(std::size_t index) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::at(index) );
//	}
//
//
//	inline reference operator[](std::size_t index)
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::operator[](index) );
//	}
//
//	inline const_reference operator[](std::size_t index) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::operator[](index) );
//	}
////////////////////////////////////////////////////////////////////////////////


	inline void set(std::size_t index, const T & arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		(*this)[index] = arg;
	}


	/*
	 ***************************************************************************
	 * GETTER / SETTER
	 * reverse access
	 ***************************************************************************
	 */

	inline reference reverse_at(std::size_t index)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}

	inline const_reference reverse_at(std::size_t index) const
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}


	inline reference reverse_get(std::size_t index)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}

	inline const_reference reverse_get(std::size_t index) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}



	inline void reverse_set(std::size_t index, const T & arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		(*this)[BaseVector::size() - 1 - index] = arg;
	}



	/*
	 ***************************************************************************
	 * SETTER
	 * reset
	 * erase - remove (<=> erase all)
	 * rremove
	 ***************************************************************************
	 */
	inline virtual void reset() override
	{
		BaseVector::clear();
	}

	using Collection<T>::reset;

	inline virtual void remove(const T & arg) override
	{
		typename BaseVector::iterator it = BaseVector::begin();
		for( ; it != BaseVector::end() ; ++it )
		{
			if( (*it) == arg )
			{
				BaseVector::erase(it);
				break;
			}
		}


		//		for( std::size_t it = 0 ; it != BaseVector::size() ; ++it )
		//		{
		//			if( BaseVector::at(it) == arg )
		//			{
		//				BaseVector::erase(BaseVector::begin() + it);
		//				break;
		//			}
		//		}
	}

	using Collection<T>::remove;


	inline void rremove(const T & arg)
	{
		typename
		BaseVector::reverse_iterator it =BaseVector::rbegin();
		for( ; it != BaseVector::rend() ; ++it )
		{
			if( (*it) == arg )
			{
				BaseVector::erase( --( it.base() ) );
				break;
			}
		}
	}

};


/**
 * MEMORY MANAGEMENT
 * DESTROY
 */
template< class T >
void destroy(Vector< T * > * & aVector)
{
	typename Vector< T * >::iterator it = aVector->begin();
	typename Vector< T * >::iterator itEnd = aVector->end();
	for( ; it != itEnd ; ++it )
	{
		sep::destroy( *it );
	}

	delete( aVector );

	aVector = nullptr;
}


template< class T >
void destroy(Vector< T > * & aVector)
{
	delete( aVector );

	aVector = nullptr;
}



}

#endif /*CONTAINER_VECTOR_H_*/
