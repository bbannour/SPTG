/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 31 mars 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILTINQUEUE_H_
#define BUILTINQUEUE_H_

#include <fml/expression/BuiltinContainer.h>

#include <common/BF.h>

#include <collection/Typedef.h>


namespace sep
{


class BuiltinQueue  :  public BuiltinList ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinQueue )
{


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinQueue(class_kind_t aClassKind )
	: BuiltinList( aClassKind )
	{
		//!! NOTHING
	}

	BuiltinQueue(class_kind_t aClassKind, avm_size_t aCapacity)
	: BuiltinList( aClassKind , aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinQueue(const BuiltinQueue & aQueue)
	: BuiltinList( aQueue )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinQueue()
	{
		//!! NOTHING
	}


	/**
	 * INTERFACE
	 */
	inline virtual void set(avm_size_t idx, const BF & arg)
	{
		iterator it = mData.begin();
		iterator endIt = mData.end();
		for( ; (it != endIt) && (idx > 0) ; ++it , --idx )
		{
			//!!! NOTHING
		}

		if( (idx == 0) && (it != endIt) )
		{
			(*it) = arg;
		}
		else
		{
			push(arg);
		}
	}


	inline virtual void resize(avm_size_t newSize)
	{
		if( mCapacity > newSize )
		{
			if( (mCapacity = size()) > newSize )
			{
				for( ; mCapacity > newSize ; --mCapacity )
				{
					pop();
				}
				return;
			}
		}
		mCapacity = newSize;
	}

	inline virtual void resize(avm_size_t newSize, const BF & arg)
	{
		if( mCapacity > newSize )
		{
			if( (mCapacity = size()) > newSize )
			{
				for( ; mCapacity > newSize ; --mCapacity )
				{
					pop();
				}
				return;
			}
		}

		if( (mCapacity = size()) < newSize )
		{
			for( ; mCapacity < newSize ; ++mCapacity )
			{
				push(arg);
			}
		}

		mCapacity = newSize;
	}


	virtual bool push(const BF & arg) = 0;

	// assign_top
	virtual bool top(const BF & arg) = 0;

	virtual BF & top() = 0;
	virtual const BF & top() const = 0;

	virtual BF pop() = 0;

	inline virtual BF pop(avm_size_t count)
	{
		BF elt;

		iterator endIt = mData.end();
		for( iterator it = mData.begin() ; (it != endIt) && (count >= 0) ; --count )
		{
			elt = pop();
		}

		return( pop() );
	}


	virtual BF pop_from(const BuiltinList & aList) const = 0;

	virtual void remove_popable(const BF & arg) = 0;

};



class BuiltinFifo  :  public BuiltinQueue ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinFifo )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinFifo )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinFifo()
	: BuiltinQueue( CLASS_KIND_T( BuiltinFifo ) )
	{
		//!! NOTHING
	}

	BuiltinFifo(avm_size_t aCapacity)
	: BuiltinQueue( CLASS_KIND_T( BuiltinFifo ) , aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinFifo(const BuiltinFifo & aFifo)
	: BuiltinQueue( aFifo )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinFifo()
	{
		//!! NOTHING
	}


	/**
	 * INTERFACE
	 */
	inline virtual bool push(const BF & arg)
	{
		if( size() < mCapacity )
		{
			mData.push_back( arg );
			return( true );
		}
		return( false );
	}

	inline virtual bool top(const BF & arg)
	{
		if( nonempty() )
		{
			mData.pop_front();
			mData.push_front( arg );
			return( true );
		}
		return( false );
	}

	inline virtual BF & top()
	{
		if ( nonempty() )
		{
			return( mData.front() );
		}
		return( BF::REF_NULL );
	}

	inline virtual const BF & top() const
	{
		if ( nonempty() )
		{
			return( mData.front() );
		}
		return( BF::REF_NULL );
	}


	inline virtual BF pop()
	{
		if ( nonempty() )
		{
			return( mData.pop_first() );
		}
		return( BF::REF_NULL );
	}


	inline virtual BF pop_from(const BuiltinList & aList) const
	{
		const_reverse_iterator endIt = mData.rend();
		for( const_reverse_iterator it = mData.rbegin() ; (it != endIt) ; ++it )
		{
			if( aList.contains(*it) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}



	inline virtual void remove_popable(const BF & arg)
	{
		reverse_iterator endIt = mData.rend();
		for( reverse_iterator it = mData.rbegin() ; (it != endIt) ; ++it )
		{
			if( (*it) == arg )
			{
				mData.erase( --( it.base() ) );

				break;
			}
		}
	}

};



class BuiltinLifo  :  public BuiltinQueue ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinLifo )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinLifo )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinLifo()
	: BuiltinQueue( CLASS_KIND_T( BuiltinLifo ) )
	{
		//!! NOTHING
	}

	BuiltinLifo(avm_size_t aCapacity)
	: BuiltinQueue( CLASS_KIND_T( BuiltinLifo ) , aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinLifo(const BuiltinLifo & aLifo)
	: BuiltinQueue( aLifo )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinLifo()
	{
		//!! NOTHING
	}


	/**
	 * INTERFACE
	 */
	inline virtual bool push(const BF & arg)
	{
		if( size() < mCapacity )
		{
			mData.push_back( arg );
			return( true );
		}
		return( false );
	}


	inline virtual bool top(const BF & arg)
	{
		if( nonempty() )
		{
			mData.pop_back();
			mData.push_back( arg );
			return( true );
		}
		return( false );
	}

	inline virtual BF & top()
	{
		if ( nonempty() )
		{
			return( mData.back() );
		}
		return( BF::REF_NULL );
	}

	inline virtual const BF & top() const
	{
		if ( nonempty() )
		{
			return( mData.back() );
		}
		return( BF::REF_NULL );
	}


	inline virtual BF pop()
	{
		if ( nonempty() )
		{
			return( mData.pop_last() );
		}
		return( BF::REF_NULL );
	}


	inline virtual BF pop_from(const BuiltinList & aList) const
	{
		const_iterator endIt = mData.end();
		for( const_iterator it = mData.begin() ; (it != endIt) ; ++it )
		{
			if( aList.contains(*it) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}


	inline virtual void remove_popable(const BF & arg)
	{
		iterator endIt = mData.end();
		for( iterator it = mData.begin() ; (it != endIt) ; ++it )
		{
			if( (*it) == arg )
			{
				mData.erase( it );

				break;
			}
		}
	}

};


}

#endif /* BUILTINQUEUE_H_ */
