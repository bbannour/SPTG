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
	virtual std::size_t capacity() const = 0;

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


	virtual std::size_t size() const override = 0;

	virtual void resize(std::size_t newSize) = 0;


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
	std::size_t mCapacity;


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

	BuiltinContainer(class_kind_t aClassKind, std::size_t aCapacity)
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
	static BuiltinContainer * create(const ContainerTypeSpecifier & containerT);


	/**
	 * GETTER - SETTER
	 * mCapacity
	 */
	inline virtual std::size_t capacity() const override
	{
		return( mCapacity );
	}

	inline virtual void setCapacity(long aCapacity) override
	{
		mCapacity = (aCapacity < 0) ? AVM_NUMERIC_MAX_SIZE_T : aCapacity;
	}


	/**
	 * INTERFACE
	 */
	/**
	 * front / first
	 * back  / last
	 */
	virtual BF & front() = 0;
	virtual BF & first() = 0;

	virtual const BF & front() const = 0;
	virtual const BF & first() const = 0;

	virtual BF & back() = 0;
	virtual BF & last() = 0;

	virtual const BF & back() const = 0;
	virtual const BF & last() const = 0;


	/**
	 * POP
	 * front / first
	 * back  / last
	 */
	virtual BF pop_front() = 0;
	virtual BF pop_first() = 0;

	virtual BF pop_back() = 0;
	virtual BF pop_last() = 0;


	virtual       BF & at(std::size_t idx) override = 0;
	virtual const BF & at(std::size_t idx) const override = 0;


	inline virtual BF & operator[](std::size_t offset) override
	{
		return( at(offset) );
	}

	inline virtual const BF & operator[](std::size_t offset) const override
	{
		return( at(offset) );
	}

	virtual       BF & get(std::size_t idx) = 0;
	virtual const BF & get(std::size_t idx) const = 0;

	virtual BF & getWritable(std::size_t offset) override = 0;

	virtual void makeWritable(std::size_t offset)  override = 0;

	virtual void set(std::size_t idx, const BF & arg)  override = 0;


	/**
	 * INTERFACE
	 */
	virtual bool add(const BF & arg) = 0;

	inline virtual bool push(const BF & arg)
	{
		return( add( arg ) );
	}

	inline virtual BF pop()
	{
		return( pop_first() );
	}


	virtual void erase(std::size_t idx) = 0;

	virtual void remove(const BF & arg) = 0;

	virtual void clear() = 0;

	void copy(const BuiltinArray & intputArray, std::size_t count);


	/**
	 * USUAL EQUAL
	 */
	int compare(const BuiltinContainer & other) const;

	bool isEQ(const BuiltinContainer & other) const;

	using BuiltinCollection::isEQ;


	inline bool isNEQ(const BuiltinContainer & other) const
	{
		return( not isEQ( other ) );
	}

	using BuiltinCollection::isNEQ;


	/**
	 * SYNTAXIC EQUAL
	 */
	bool isSEQ(const BuiltinContainer & other) const;

	inline bool isNSEQ(const BuiltinContainer & other) const
	{
		return( not BuiltinContainer::isSEQ( other ) );
	}


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

	BuiltinList(std::size_t aCapacity)
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

	BuiltinList(class_kind_t aClassKind, std::size_t aCapacity)
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


	/**
	 * front / first
	 * back  / last
	 */
	inline virtual BF & front() override
	{
		return( mData.front() );
	}

	inline virtual BF & first() override
	{
		return( mData.first() );
	}

	inline virtual const BF & front() const override
	{
		return( mData.front() );
	}

	inline virtual const BF & first() const override
	{
		return( mData.first() );
	}


	inline virtual BF & back() override
	{
		return( mData.back() );
	}

	inline virtual BF & last() override
	{
		return( mData.last() );
	}

	inline virtual const BF & back() const override
	{
		return( mData.back() );
	}

	inline virtual const BF & last() const override
	{
		return( mData.last() );
	}


	/**
	 * POP
	 * front / first
	 * back  / last
	 */
	virtual BF pop_front() override
	{
		return( mData.pop_first() );
	}

	virtual BF pop_first() override
	{
		return( mData.pop_first() );
	}

	virtual BF pop_back() override
	{
		return( mData.pop_last() );
	}

	virtual BF pop_last() override
	{
		return( mData.pop_last() );
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const override
	{
		return( mData.empty() );
	}

	inline virtual bool nonempty() const override
	{
		return( mData.nonempty() );
	}

	inline virtual bool singleton() const override
	{
		return( mData.singleton() );
	}

	inline virtual bool populated() const override
	{
		return( mData.populated() );
	}


	inline virtual std::size_t size() const override
	{
		return( mData.size() );
	}

	inline virtual void resize(std::size_t newSize) override
	{
		mData.resize(newSize);
	}


	/**
	 * INTERFACE
	 */
	virtual BF & at(std::size_t idx) override
	{
		return( mData.at(idx) );
	}

	virtual const BF & at(std::size_t idx) const override
	{
		return( mData.at(idx) );
	}


	virtual BF & get(std::size_t idx) override
	{
		return( mData.get(idx) );
	}

	virtual const BF & get(std::size_t idx) const override
	{
		return( mData.get(idx) );
	}

	inline virtual BF & getWritable(std::size_t idx) override
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

	inline virtual void makeWritable(std::size_t idx) override
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

	inline virtual void set(std::size_t idx, const BF & arg) override
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


	inline virtual bool add(const BF & arg) override
	{
		if( size() < mCapacity)
		{
			mData.append(arg);
			return( true );
		}
		return( false );
	}


	inline virtual bool contains(const BF & arg) const override
	{
		return( mData.contains(arg) );
	}


	inline bool intersect(const BuiltinList & aBuiltin) const
	{
		return( mData.intersect(aBuiltin.mData) );
	}



	inline virtual void erase(std::size_t idx) override
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


	inline virtual void remove(const BF & arg) override
	{
		mData.remove(arg);
	}

	inline virtual void clear() override
	{
		mData.clear();
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	virtual void toStream(OutStream & os) const override
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

	BuiltinVector(std::size_t aCapacity)
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

	BuiltinVector(class_kind_t aClassKind, std::size_t aCapacity)
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


	/**
	 * front / first
	 * back  / last
	 */
	inline virtual BF & front() override
	{
		return( mData.front() );
	}

	inline virtual BF & first() override
	{
		return( mData.first() );
	}

	inline virtual const BF & front() const override
	{
		return( mData.front() );
	}

	inline virtual const BF & first() const override
	{
		return( mData.first() );
	}


	inline virtual BF & back() override
	{
		return( mData.back() );
	}

	inline virtual BF & last() override
	{
		return( mData.last() );
	}

	inline virtual const BF & back() const override
	{
		return( mData.back() );
	}

	inline virtual const BF & last() const override
	{
		return( mData.last() );
	}


	/**
	 * POP
	 * front / first
	 * back  / last
	 */
	virtual BF pop_front() override
	{
		return( mData.pop_first() );
	}

	virtual BF pop_first() override
	{
		return( mData.pop_first() );
	}

	virtual BF pop_back() override
	{
		return( mData.pop_last() );
	}

	virtual BF pop_last() override
	{
		return( mData.pop_last() );
	}


	/*
	 ***************************************************************************
	 * GETTER
	 * emptiness
	 ***************************************************************************
	 */
	inline virtual bool empty() const override
	{
		return( mData.empty() );
	}

	inline virtual bool nonempty() const override
	{
		return( mData.nonempty() );
	}

	inline virtual bool singleton() const override
	{
		return( mData.singleton() );
	}

	inline virtual bool populated() const override
	{
		return( mData.populated() );
	}


	inline virtual std::size_t size() const override
	{
		return( mData.size() );
	}

	inline virtual void resize(std::size_t newSize) override
	{
		mData.resize(newSize);
	}




	/**
	 * INTERFACE
	 */
	inline virtual BF & at(std::size_t idx) override
	{
		return( mData.at(idx) );
	}

	inline virtual const BF & at(std::size_t idx) const override
	{
		return( mData.at(idx) );
	}


	inline virtual BF & operator[](std::size_t offset) override
	{
		return( mData.operator[](offset) );
	}

	inline virtual const BF & operator[](std::size_t offset) const override
	{
		return( mData.operator[](offset) );
	}


	inline virtual BF & get(std::size_t idx) override
	{
		return( mData.get(idx) );
	}

	inline virtual const BF & get(std::size_t idx) const override
	{
		return( mData.get(idx) );
	}


	inline virtual BF & getWritable(std::size_t offset) override
	{
		mData[offset].makeWritable();

		return( mData[offset] );
	}

	inline virtual void makeWritable(std::size_t offset) override
	{
		mData[offset].makeWritable();
	}


	inline virtual void set(std::size_t idx, const BF & arg) override
	{
		mData.set(idx, arg);
	}


	inline virtual bool add(const BF & arg) override
	{
		if( size() < mCapacity)
		{
			mData.append(arg);
			return( true );
		}
		return( false );
	}


	inline virtual bool contains(const BF & arg) const override
	{
		return( mData.contains(arg) );
	}


	inline virtual void erase(std::size_t idx) override
	{
		mData.erase( mData.begin() + idx );
	}


	inline virtual void remove(const BF & arg) override
	{
		mData.remove(arg);
	}

	inline virtual void clear() override
	{
		mData.clear();
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline virtual void toStream(OutStream & os) const override
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

	BuiltinReverseVector(std::size_t aCapacity)
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
	inline virtual BF & at(std::size_t idx) override
	{
		return( mData.reverse_at(idx) );
	}

	inline virtual const BF & at(std::size_t idx) const override
	{
		return( mData.reverse_at(idx) );
	}


	inline virtual BF & operator[](std::size_t offset) override
	{
		return( mData.reverse_at(offset) );
	}

	inline virtual const BF & operator[](std::size_t offset) const override
	{
		return( mData.reverse_at(offset) );
	}


	inline virtual BF & get(std::size_t idx) override
	{
		return( mData.reverse_get(idx) );
	}

	inline virtual const BF & get(std::size_t idx) const override
	{
		return( mData.reverse_get(idx) );
	}

	inline virtual BF & getWritable(std::size_t offset) override
	{
		mData.reverse_get(offset).makeWritable();

		return( mData.reverse_get(offset) );
	}

	inline virtual void makeWritable(std::size_t offset) override
	{
		mData.reverse_get(offset).makeWritable();
	}


	inline virtual void set(std::size_t idx, const BF & arg) override
	{
		mData.reverse_set(idx, arg);
	}

	/**
	 * POP
	 * front / first
	 * back  / last
	 */
	virtual BF pop_front() override
	{
		return( mData.pop_last() );
	}

	virtual BF pop_first() override
	{
		return( mData.pop_last() );
	}

	virtual BF pop_back() override
	{
		return( mData.pop_first() );
	}

	virtual BF pop_last() override
	{
		return( mData.pop_first() );
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

	BuiltinSet(std::size_t aCapacity)
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
	inline virtual bool add(const BF & arg) override
	{
		if( size() < mCapacity )
		{
//			for( const auto & it : (*this) )
//			{
//				if( arg.strEQ( it ) )
//				{
//					return( true );
//				}
//			}
//			mData.push_back( arg );


			if( not contains(arg) )
			{
				mData.push_back( arg );
			}
			return( true );
		}
		return( false );
	}

	inline virtual void set(std::size_t idx, const BF & arg) override
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

	BuiltinBag(std::size_t aCapacity)
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
	inline virtual void set(std::size_t idx, const BF & arg) override
	{
		BuiltinList::set(idx, arg);
	}

};



}

#endif /* BUILTINCONTAINER_H_ */
