/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BUILTINCONTAINER_H_
#define BUILTINCONTAINER_H_

#include <fml/builtin/BuiltinForm.h>

#include <collection/BFContainer.h>


namespace sep
{


class BuiltinArray;
class ContainerTypeSpecifier;


class BuiltinCollection  :
		public BuiltinForm ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinCollection )
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinCollection(class_kind_t aClassKind)
	: BuiltinForm( aClassKind )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinCollection(const BuiltinCollection & aBuiltinCollection)
	: BuiltinForm( aBuiltinCollection )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinCollection()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	virtual avm_size_t capacity() const = 0;

	inline long realCapacity() const
	{
		return( (capacity() == AVM_NUMERIC_MAX_SIZE_T)? -1 : capacity() );
	}

	virtual void setCapacity(long aCapacity) = 0;

	inline bool isFinite() const
	{
		return( capacity() < AVM_NUMERIC_MAX_SIZE_T );
	}

	inline bool isInfinite() const
	{
		return( capacity() == AVM_NUMERIC_MAX_SIZE_T );
	}


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

	inline virtual bool full() const
	{
		return( size() == capacity() );
	}


	virtual avm_size_t size() const = 0;

	virtual void resize(avm_size_t newSize) = 0;


	/**
	 * INTERFACE
	 */
	virtual bool contains(const BF & arg) const = 0;

};


class BuiltinContainer  :
		public BuiltinCollection,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinContainer )
{

protected:
	/**
	 * ATTRIBUTES
	 */
	avm_size_t mCapacity;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinContainer(class_kind_t aClassKind)
	: BuiltinCollection( aClassKind ),
	mCapacity( AVM_NUMERIC_MAX_SIZE_T )
	{
		//!! NOTHING
	}

	BuiltinContainer(class_kind_t aClassKind, avm_size_t aCapacity)
	: BuiltinCollection( aClassKind ),
	mCapacity( aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinContainer(const BuiltinContainer & aBuiltinContainer)
	: BuiltinCollection( aBuiltinContainer ),
	mCapacity( aBuiltinContainer.mCapacity )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinContainer()
	{
		mCapacity = 0;
	}


	/**
	 * CREATION
	 */
	static BuiltinContainer * create(ContainerTypeSpecifier * containerT);


	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	inline avm_size_t capacity() const
	{
		return( mCapacity );
	}

	inline void setCapacity(long aCapacity)
	{
		mCapacity = (aCapacity < 0) ? AVM_NUMERIC_MAX_SIZE_T : aCapacity;
	}


	/**
	 * INTERFACE
	 */
	virtual       BF & at(avm_size_t idx) = 0;
	virtual const BF & at(avm_size_t idx) const = 0;


	inline virtual BF & operator[](avm_size_t offset)
	{
		return( at(offset) );
	}

	inline virtual const BF & operator[](avm_size_t offset) const
	{
		return( at(offset) );
	}

	virtual       BF & get(avm_size_t idx) = 0;
	virtual const BF & get(avm_size_t idx) const = 0;

	virtual BF & getWritable(avm_size_t offset) = 0;

	virtual void makeWritable(avm_size_t offset) = 0;

	virtual void set(avm_size_t idx, const BF & arg) = 0;


	/**
	 * INTERFACE
	 */
	virtual bool add(const BF & arg) = 0;

	inline virtual bool push(const BF & arg)
	{
		return( add( arg ) );
	}


	virtual void erase(avm_size_t idx) = 0;

	virtual void remove(const BF & arg) = 0;

	virtual void clear() = 0;

	void copy(BuiltinArray * intputArray, avm_size_t count);

};



class BuiltinList :
		public BuiltinContainer,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinList )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinList )

protected:
	/**
	 * TYPEDEF
	 */
	typedef BFList                     list_type;

public:
	typedef list_type::iterator        iterator;
	typedef list_type::const_iterator  const_iterator;

	typedef list_type::reverse_iterator        reverse_iterator;
	typedef list_type::const_reverse_iterator  const_reverse_iterator;


protected:
	/**
	 * ATTRIBUTES
	 */
	list_type mData;

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinList()
	: BuiltinContainer(CLASS_KIND_T( BuiltinList ) ),
	mData( )
	{
		//!! NOTHING
	}

	BuiltinList(avm_size_t aCapacity)
	: BuiltinContainer(CLASS_KIND_T( BuiltinList ), aCapacity ),
	mData( )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	BuiltinList(class_kind_t aClassKind)
	: BuiltinContainer( aClassKind ),
	mData( )
	{
		//!! NOTHING
	}

	BuiltinList(class_kind_t aClassKind, avm_size_t aCapacity)
	: BuiltinContainer( aClassKind , aCapacity ),
	mData( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinList(const BuiltinList & aBuiltinList)
	: BuiltinContainer( aBuiltinList ),
	mData( aBuiltinList.mData )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinList()
	{
		clear();
	}


	/**
	 * ITERATOR
	 */
	inline iterator begin()
	{
		return( mData.begin() );
	}

	inline const_iterator begin() const
	{
		return( mData.begin() );
	}


	inline iterator end()
	{
		return( mData.end() );
	}

	inline const_iterator end() const
	{
		return( mData.end() );
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const
	{
		return( mData.empty() );
	}

	inline virtual bool nonempty() const
	{
		return( mData.nonempty() );
	}

	inline virtual bool singleton() const
	{
		return( mData.singleton() );
	}

	inline virtual bool populated() const
	{
		return( mData.populated() );
	}


	inline virtual avm_size_t size() const
	{
		return( mData.size() );
	}

	inline virtual void resize(avm_size_t newSize)
	{
		mData.resize(newSize);
	}


	/**
	 * INTERFACE
	 */
	virtual BF & at(avm_size_t idx)
	{
		return( mData.at(idx) );
	}

	virtual const BF & at(avm_size_t idx) const
	{
		return( mData.at(idx) );
	}


	virtual BF & get(avm_size_t idx)
	{
		return( mData.get(idx) );
	}

	virtual const BF & get(avm_size_t idx) const
	{
		return( mData.get(idx) );
	}

	inline virtual BF & getWritable(avm_size_t idx)
	{
		iterator it = mData.begin();
		iterator endIt = mData.end();
		for( ; (it != endIt) && (idx > 0) ; ++it , --idx )
		{
			//!!! NOTHING
		}

		if( (idx == 0) && (it != endIt) )
		{
			(*it).makeWritable();

			return( *it );
		}
		else
		{
			mData.last().makeWritable();

			return( mData.last() );
		}
	}

	inline virtual void makeWritable(avm_size_t idx)
	{
		iterator it = mData.begin();
		iterator endIt = mData.end();
		for( ; (it != endIt) && (idx > 0) ; ++it , --idx )
		{
			//!!! NOTHING
		}

		if( (idx == 0) && (it != endIt) )
		{
			(*it).makeWritable();
		}
		else
		{
			mData.last().makeWritable();
		}
	}

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
			add(arg);
		}
	}


	inline virtual bool add(const BF & arg)
	{
		if( size() < mCapacity)
		{
			mData.append(arg);
			return( true );
		}
		return( false );
	}


	inline virtual bool contains(const BF & arg) const
	{
		return( mData.contains(arg) );
	}


	inline virtual bool intersect(const BuiltinList & aBuiltin) const
	{
		return( mData.intersect(aBuiltin.mData) );
	}



	inline virtual void erase(avm_size_t idx)
	{
		if( mData.nonempty() )
		{
			iterator it = mData.begin();
			iterator endIt = mData.end();
			for( ; (it != endIt) && (idx > 0) ; ++it , --idx )
			{
				//!!! NOTHING
			}

			if( (idx == 0) && (it != endIt) )
			{
				mData.erase(it);
			}
		}
	}


	inline virtual void remove(const BF & arg)
	{
		mData.remove(arg);
	}

	inline virtual void clear()
	{
		mData.clear();
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	virtual void toStream(OutStream & os) const
	{
		os << TAB;

AVM_IF_DEBUG_FLAG( DATA )

		os << "<" << classKindName() << ">";

AVM_ENDIF_DEBUG_FLAG( DATA )

		os << "{ ";
		if( mData.nonempty() )
		{
			const_iterator it = mData.begin();
			const_iterator endIt = mData.end();
			os << (*it).str();
			for( ++it ; it != endIt ; ++it )
			{
				os << " , " << (*it).str();
			}
		}
		os << " }" << EOL_FLUSH;
	}

};


class BuiltinVector :
		public BuiltinContainer,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinVector )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinVector )

protected:
	/**
	 * TYPEDEF
	 */
	typedef BFVector                     vector_type;

public:
	typedef vector_type::iterator        iterator;
	typedef vector_type::const_iterator  const_iterator;

protected:
	/**
	 * ATTRIBUTES
	 */
	vector_type mData;

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinVector()
	: BuiltinContainer( CLASS_KIND_T( BuiltinVector ) ),
	mData( )
	{
		//!! NOTHING
	}

	BuiltinVector(avm_size_t aCapacity)
	: BuiltinContainer( CLASS_KIND_T( BuiltinVector ), aCapacity),
	mData( )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinVector(const BuiltinVector & aBuiltinVector)
	: BuiltinContainer( aBuiltinVector ),
	 mData( aBuiltinVector.mData )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinVector(class_kind_t aClassKind)
	: BuiltinContainer( aClassKind ),
	mData( )
	{
		//!! NOTHING
	}

	BuiltinVector(class_kind_t aClassKind, avm_size_t aCapacity)
	: BuiltinContainer( aClassKind , aCapacity ),
	mData( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinVector()
	{
		clear();
	}


	/**
	 * ITERATOR
	 */
	inline iterator begin()
	{
		return( mData.begin() );
	}

	inline const_iterator begin() const
	{
		return( mData.begin() );
	}


	inline iterator end()
	{
		return( mData.end() );
	}

	inline const_iterator end() const
	{
		return( mData.end() );
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const
	{
		return( mData.empty() );
	}

	inline virtual bool nonempty() const
	{
		return( mData.nonempty() );
	}

	inline virtual bool singleton() const
	{
		return( mData.singleton() );
	}

	inline virtual bool populated() const
	{
		return( mData.populated() );
	}


	inline virtual avm_size_t size() const
	{
		return( mData.size() );
	}

	inline virtual void resize(avm_size_t newSize)
	{
		mData.resize(newSize);
	}




	/**
	 * INTERFACE
	 */
	virtual BF & at(avm_size_t idx)
	{
		return( mData.at(idx) );
	}

	virtual const BF & at(avm_size_t idx) const
	{
		return( mData.at(idx) );
	}


	inline virtual BF & operator[](avm_size_t offset)
	{
		return( mData.operator[](offset) );
	}

	inline virtual const BF & operator[](avm_size_t offset) const
	{
		return( mData.operator[](offset) );
	}


	virtual BF & get(avm_size_t idx)
	{
		return( mData.get(idx) );
	}

	virtual const BF & get(avm_size_t idx) const
	{
		return( mData.get(idx) );
	}


	inline BF & getWritable(avm_size_t offset)
	{
		mData[offset].makeWritable();

		return( mData[offset] );
	}

	inline void makeWritable(avm_size_t offset)
	{
		mData[offset].makeWritable();
	}


	inline virtual void set(avm_size_t idx, const BF & arg)
	{
		mData.set(idx, arg);
	}


	inline virtual bool add(const BF & arg)
	{
		if( size() < mCapacity)
		{
			mData.append(arg);
			return( true );
		}
		return( false );
	}


	inline virtual bool contains(const BF & arg) const
	{
		return( mData.contains(arg) );
	}


	inline virtual void erase(avm_size_t idx)
	{
		mData.erase( mData.begin() + idx );
	}


	inline virtual void remove(const BF & arg)
	{
		mData.remove(arg);
	}

	inline virtual void clear()
	{
		mData.clear();
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	virtual void toStream(OutStream & os) const
	{
		os << TAB;

AVM_IF_DEBUG_FLAG( DATA )

		os << "<" << classKindName() << ">";

AVM_ENDIF_DEBUG_FLAG( DATA )

		os << "[ ";
		if( mData.nonempty() )
		{
			const_iterator it = mData.begin();
			const_iterator endIt = mData.end();
			os << (*it).str();
			for( ++it ; it != endIt ; ++it )
			{
				os << " , " << (*it).str();
			}
		}
		os << " ]" << EOL_FLUSH;
	}

};



class BuiltinReverseVector  :  public BuiltinVector ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinReverseVector )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinReverseVector )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinReverseVector()
	: BuiltinVector(CLASS_KIND_T( BuiltinReverseVector ) )
	{
		//!! NOTHING
	}

	BuiltinReverseVector(avm_size_t aCapacity)
	: BuiltinVector(CLASS_KIND_T( BuiltinReverseVector ), aCapacity)
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinReverseVector(const BuiltinReverseVector & aBuiltinRVector)
	: BuiltinVector( aBuiltinRVector )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinReverseVector()
	{
		clear();
	}


	/**
	 * INTERFACE
	 */
	virtual BF & at(avm_size_t idx)
	{
		return( mData.reverse_at(idx) );
	}

	virtual const BF & at(avm_size_t idx) const
	{
		return( mData.reverse_at(idx) );
	}


	inline virtual BF & operator[](avm_size_t offset)
	{
		return( mData.reverse_at(offset) );
	}

	inline virtual const BF & operator[](avm_size_t offset) const
	{
		return( mData.reverse_at(offset) );
	}


	virtual BF & get(avm_size_t idx)
	{
		return( mData.reverse_get(idx) );
	}

	virtual const BF & get(avm_size_t idx) const
	{
		return( mData.reverse_get(idx) );
	}

	inline BF & getWritable(avm_size_t offset)
	{
		mData.reverse_get(offset).makeWritable();

		return( mData.reverse_get(offset) );
	}

	inline void makeWritable(avm_size_t offset)
	{
		mData.reverse_get(offset).makeWritable();
	}


	inline virtual void set(avm_size_t idx, const BF & arg)
	{
		mData.reverse_set(idx, arg);
	}

};



class BuiltinSet  :  public BuiltinList ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinSet )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinSet )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinSet()
	: BuiltinList( CLASS_KIND_T( BuiltinSet ) )
	{
		//!! NOTHING
	}

	BuiltinSet(avm_size_t aCapacity)
	: BuiltinList( CLASS_KIND_T( BuiltinSet ) , aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinSet(const BuiltinSet & aBuiltinSet)
	: BuiltinList( aBuiltinSet )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinSet()
	{
	}


	/**
	 * INTERFACE
	 */
	inline virtual bool add(const BF & arg)
	{
		if( size() < mCapacity )
		{
			if( not contains(arg) )
			{
				mData.push_back( arg );
			}
			return( true );
		}
		return( false );
	}

	inline virtual void set(avm_size_t idx, const BF & arg)
	{
		BuiltinList::remove(arg);
		BuiltinList::set(idx, arg);
	}

};



class BuiltinBag  :  public BuiltinList ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( BuiltinBag )
{

	AVM_DECLARE_CLONABLE_CLASS( BuiltinBag )


public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BuiltinBag()
	: BuiltinList( CLASS_KIND_T( BuiltinBag ) )
	{
		//!! NOTHING
	}

	BuiltinBag(avm_size_t aCapacity)
	: BuiltinList( CLASS_KIND_T( BuiltinBag ) , aCapacity )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BuiltinBag(const BuiltinBag & aBuiltinBag)
	: BuiltinList( aBuiltinBag )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BuiltinBag()
	{
		//!! NOTHING
	}


	/**
	 * INTERFACE
	 */
	inline virtual void set(avm_size_t idx, const BF & arg)
	{
		BuiltinList::set(idx, arg);
	}

};



}

#endif /* BUILTINCONTAINER_H_ */
