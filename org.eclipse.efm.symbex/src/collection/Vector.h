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
#include <base/SmartPointerUtil.h>

#include <collection/Collection.h>


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
	explicit Vector(avm_size_t count)
	: BaseVector(count)
	{
		//!! NOTHING
	}

	explicit Vector(avm_size_t count, const T & elem)
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
	inline virtual void push_back(const T & arg)
	{
		BaseVector::push_back(arg);
	}


	inline virtual void push_back(const std::list< T > & aCollection)
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


	inline virtual void push_back(const std::vector< T > & aCollection)
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



	inline virtual void push_front(const T & arg)
	{
		BaseVector::insert(BaseVector::begin(), arg);
	}

	inline virtual void push_front(const std::list< T > & aCollection)
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


	inline virtual void push_front(const std::vector< T > & aCollection)
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
	inline virtual bool empty() const
	{
		return( BaseVector::empty() );
	}

	inline virtual bool nonempty() const
	{
		return( not BaseVector::empty() );
	}

	inline virtual bool singleton() const
	{
		return( BaseVector::size() == 1 );
	}

	inline virtual bool populated() const
	{
		return( BaseVector::size() > 1 );
	}


	/**
	 * contains a particular element
	 */
	inline virtual bool contains(const T & arg) const
	{
		typename
		BaseVector::const_iterator it = BaseVector::begin();
		typename
		BaseVector::const_iterator itEnd = BaseVector::end();
		for( ; it != itEnd ; ++it )
		{
			if( (*it) == arg )
			{
				return( true );
			}
		}

		//		for( avm_size_t it = 0 ; it != BaseVector::size() ; ++it )
		//		{
		//			if( BaseVector::at(it) == arg )
		//			{
		//				return( true );
		//			}
		//		}

		return( false );
	}


	inline virtual bool contains(const std::vector< T > & aCollection)
	{
		typename
		std::vector< T >::const_iterator it = aCollection.begin();
		typename
		std::vector< T >::const_iterator itEnd = aCollection.end();
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


	template< typename U >
	inline int find(U arg) const
	{
		for( avm_size_t it = 0 ; it != BaseVector::size() ; ++it )
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
	inline virtual void append(const T & arg)
	{
		BaseVector::push_back(arg);
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

	inline virtual void append(const T & arg1,
			const T & arg2, const T & arg3, const T & arg4)
	{
		append(arg1);
		append(arg2);
		append(arg3);
		append(arg4);
	}

	inline virtual void append(const T & arg1, const T & arg2,
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
			push_back(anArrayOfArgument[i]);
		}
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
	 * add_union
	 ***************************************************************************
	 */
	inline virtual void add_union(const T & arg)
	{
		if( not contains(arg) )
		{
			BaseVector::push_back(arg);
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
		return( BaseVector::front() );
	}

	inline virtual const_reference first() const
	{
		return( BaseVector::front() );
	}

	inline virtual reference getArg1()
	{
		return  get(0);
	}

	inline virtual const_reference getArg1() const
	{
		return  get(0);
	}


	inline virtual void pop_front()
	{
		BaseVector::erase(BaseVector::begin());
	}


	inline virtual T pop_first()
	{
		T theFirst = BaseVector::front();

		BaseVector::erase( BaseVector::begin() );

		return( theFirst );
	}

	inline virtual void pop_first_to(T & theFirst)
	{
		theFirst = BaseVector::front();

		BaseVector::erase( BaseVector::begin() );
	}

	inline virtual void remove_first()
	{
		BaseVector::erase( BaseVector::begin() );
	}


	inline virtual reference second()
	{
		return( get(1) );
	}

	inline virtual const_reference second() const
	{
		return( get(1) );
	}

	inline virtual reference getArg2()
	{
		return  get(1);
	}

	inline virtual const_reference getArg2() const
	{
		return  get(1);
	}


	inline virtual reference third()
	{
		return( get(2) );
	}

	inline virtual const_reference third() const
	{
		return( get(2) );
	}

	inline virtual reference getArg3()
	{
		return  get(2);
	}

	inline virtual const_reference getArg3() const
	{
		return  get(2);
	}


	inline virtual reference fourth()
	{
		return( get(3) );
	}

	inline virtual const_reference fourth() const
	{
		return( get(3) );
	}

	inline virtual reference getArg4()
	{
		return  get(3);
	}

	inline virtual const_reference getArg4() const
	{
		return  get(3);
	}


	inline virtual reference fifth()
	{
		return( get(4) );
	}

	inline virtual const_reference fifth() const
	{
		return( get(4) );
	}

	inline virtual reference getArg5()
	{
		return  get(4);
	}

	inline virtual const_reference getArg5() const
	{
		return  get(4);
	}


	inline virtual reference sixth()
	{
		return( get(5) );
	}

	inline virtual const_reference sixth() const
	{
		return( get(5) );
	}

	inline virtual reference getArg6()
	{
		return  get(5);
	}

	inline virtual const_reference getArg6() const
	{
		return  get(5);
	}


	inline virtual reference seventh()
	{
		return  get(6);
	}

	inline virtual const_reference seventh() const
	{
		return  get(6);
	}

	inline virtual reference getArg7()
	{
		return  get(6);
	}

	inline virtual const_reference getArg7() const
	{
		return  get(6);
	}


	inline virtual reference last()
	{
		return( BaseVector::back() );
	}

	inline virtual const_reference last() const
	{
		return( BaseVector::back() );
	}


	inline virtual T pop_last()
	{
		T theLast = BaseVector::back();

		BaseVector::pop_back();

		return( theLast );
	}

	inline virtual void pop_last_to(T & theLast)
	{
		theLast = BaseVector::back();

		BaseVector::pop_back();
	}

	inline virtual void remove_last()
	{
		BaseVector::pop_back();
	}

	inline virtual reference get(avm_size_t index)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::at(index) );
	}

	inline virtual const_reference get(avm_size_t index) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::at(index) );
	}

////////////////////////////////////////////////////////////////////////////////
//////// UNCOMMENT FOR << vector::_M_range_check >> EXCEPTION DEBUGGING ////////
////////////////////////////////////////////////////////////////////////////////
//
//	inline virtual reference at(avm_size_t index)
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::at(index) );
//	}
//
//	inline virtual const_reference at(avm_size_t index) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::at(index) );
//	}
//
//
//	inline virtual reference operator[](avm_size_t index)
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::operator[](index) );
//	}
//
//	inline virtual const_reference operator[](avm_size_t index) const
//	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;
//
//		return( BaseVector::operator[](index) );
//	}
////////////////////////////////////////////////////////////////////////////////


	inline virtual void set(avm_size_t index, const T & arg)
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

	inline virtual reference reverse_at(avm_size_t index)
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}

	inline virtual const_reference reverse_at(avm_size_t index) const
	{
//		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
//				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}


	inline virtual reference reverse_get(avm_size_t index)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}

	inline virtual const_reference reverse_get(avm_size_t index) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		return( BaseVector::
				at(BaseVector::size() - 1 - index) );
	}



	inline virtual void reverse_set(avm_size_t index, const T & arg)
	{
		AVM_OS_ASSERT_FATAL_ARRAY_INDEX_EXIT(index, BaseVector::size())
				<< SEND_EXIT;

		(*this)[BaseVector::size() - 1 - index] = arg;
	}



	/*
	 ***************************************************************************
	 * SETTER
	 * reset
	 ***************************************************************************
	 */
	inline virtual void reset(const T & arg)
	{
		BaseVector::clear();

		append(arg);
	}

	inline virtual void reset(const T & arg1, const T & arg2)
	{
		BaseVector::clear();

		append(arg1);
		append(arg2);
	}

	inline virtual void reset(const T & arg1, const T & arg2, const T & arg3)
	{
		BaseVector::clear();

		append(arg1);
		append(arg2);
		append(arg3);
	}

	inline virtual void reset(const T & arg1,
			const T & arg2, const T & arg3, const T & arg4)
	{
		BaseVector::clear();

		append(arg1);
		append(arg2);
		append(arg3);
		append(arg4);
	}

	inline virtual void reset(const T & arg1, const T & arg2,
			const T & arg3, const T & arg4, const T & arg5)
	{
		BaseVector::clear();

		append(arg1);
		append(arg2);
		append(arg3);
		append(arg4);
		append(arg5);
	}


	inline virtual void reset(T* anArrayOfArgument, int anArgSize)
	{
		BaseVector::clear();

		for (int i = 0 ; i < anArgSize ; ++i)
		{
			push_back(anArrayOfArgument[i]);
		}
	}


	inline virtual void reset(const std::list< T > & aCollection)
	{
		BaseVector::clear();

		push_back(aCollection);
	}

	inline virtual void reset(const std::vector< T > & aCollection)
	{
		BaseVector::clear();

		push_back(aCollection);
	}


	template< typename _TOE >
	inline void reset(const std::list< _TOE > & aCollection)
	{
		BaseVector::clear();

		push_back(aCollection);
	}

	template< typename _TOE >
	inline void reset(const std::vector< _TOE > & aCollection)
	{
		BaseVector::clear();

		push_back(aCollection);
	}

	/**
	 * erase - remove (<=> erase all)
	 *
	 */
	inline virtual void remove(const T & arg)
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


		//		for( avm_size_t it = 0 ; it != BaseVector::size() ; ++it )
		//		{
		//			if( BaseVector::at(it) == arg )
		//			{
		//				BaseVector::erase(BaseVector::begin() + it);
		//				break;
		//			}
		//		}
	}

	inline virtual void rremove(const T & arg)
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





template< typename T >
class APVector  :  public Vector< T >
{
public:
	/**
	 * TYPEDEF
	 */
	typedef T       & reference;
	typedef const T & const_reference;

	typedef Vector< T >  BaseAPVector;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	APVector()
	: BaseAPVector()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	APVector(const APVector & aVector)
	: BaseAPVector( )
	{
		typename BaseAPVector::const_iterator it = aVector.begin();
		typename BaseAPVector::const_iterator itEnd = aVector.end();
		for( ; it != itEnd ; ++it )
		{
			BaseAPVector::push_back( sep::incrReferenceCount( *it ) );
		}
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~APVector()
	{
		typename
		BaseAPVector::const_iterator it = BaseAPVector::begin();
		typename
		BaseAPVector::const_iterator itEnd = BaseAPVector::end();
		for( ; it != itEnd ; ++it )
		{
			sep::destroy( *it );
		}
	}

	/**
	 * CLEAR
	 */
	void clear()
	{
		while( BaseAPVector::nonempty() )
		{
			sep::destroy( BaseAPVector::pop_last() );
		}

		BaseAPVector::clear();
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

	aVector = NULL;
}


template< class T >
void destroy(Vector< T > * & aVector)
{
	delete( aVector );

	aVector = NULL;
}



}

#endif /*CONTAINER_VECTOR_H_*/
