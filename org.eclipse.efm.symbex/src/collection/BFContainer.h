/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BFCONTAINER_H_
#define BFCONTAINER_H_

#include <common/AvmObject.h>
#include <common/AvmPointer.h>
#include <common/BF.h>
#include <common/NamedElement.h>

#include <collection/Collection.h>
#include <collection/Array.h>
#include <collection/List.h>
#include <collection/Multiset.h>
#include <collection/Pair.h>
#include <collection/Set.h>
#include <collection/Vector.h>


namespace sep
{


class ObjectElement;


////////////////////////////////////////////////////////////////////////////////
// TYPEDEF FOR COLLECTION < BF >
////////////////////////////////////////////////////////////////////////////////

typedef Collection < BF > BFCollection;
//typedef     List < BF > BFList;
typedef      Array < BF > ArrayOfBF;
//typedef   Vector < BF > BFVector;
typedef   Multiset < BF > BFMultiset;
typedef        Set < BF > BFSet;



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// List of BF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class BFList  :  public List < BF >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef List< BF >    BaseListOfBF;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BFList()
	: BaseListOfBF()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BFList(const BFList & aList)
	: BaseListOfBF( aList )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BFList()
	{
		BaseListOfBF::clear();
	}


	/**
	 * SAVE
	 */
	inline void save( Element * anElement )
	{
		BaseListOfBF::append( BF( anElement) );
	}


	////////////////////////////////////////////////////////////////////////////
	// raw iterator
	////////////////////////////////////////////////////////////////////////////

	template< class rawT >
	class raw_iterator  :  public BFList::iterator
	{
	public:
		raw_iterator()
		: BFList::iterator( )
		{
			//!! NOTHING
		}

		raw_iterator(const BFList::iterator & anIterator)
		: BFList::iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT * () const
		{
			BF & current = BFList::iterator::operator*();

			return( current.to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			BF & current = BFList::iterator::operator*();

			return( current.to_ptr< rawT >() );
		}

	};


	////////////////////////////////////////////////////////////////////////////
	// const raw iterator
	////////////////////////////////////////////////////////////////////////////

	template< class rawT >
	class const_raw_iterator  :  public BFList::const_iterator
	{
	public:
		const_raw_iterator()
		: BFList::const_iterator( )
		{
			//!! NOTHING
		}

		const_raw_iterator(const BFList::const_iterator & anIterator)
		: BFList::const_iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT * () const
		{
			const BF & current = BFList::const_iterator::operator*();

			return( current.to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			const BF & current = BFList::const_iterator::operator*();

			return( current.to_ptr< rawT >() );
		}

	};

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Array of BF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

//class ArrayOfBF  :  public Array < BF >
//{
//
//public:
//	/**
//	 * TYPEDEF
//	 */
//	typedef Array < BF >    BaseArrayOfBF;
//
//
//public:
//	/**
//	 * CONSTRUCTOR
//	 * Default
//	 */
//	ArrayOfBF()
//	: BaseArrayOfBF()
//	{
//		//!! NOTHING
//	}
//
//	/**
//	 * CONSTRUCTOR
//	 * Copy
//	 */
//	ArrayOfBF(const ArrayOfBF & anArray)
//	: BaseArrayOfBF( anArray )
//	{
//		//!! NOTHING
//	}
//
//	/**
//	 * CONSTRUCTOR
//	 * Others
//	 */
//	explicit ArrayOfBF(avm_size_t count)
//	: BaseArrayOfBF(count)
//	{
//		//!! NOTHING
//	}
//
//	explicit ArrayOfBF(avm_size_t count, const BF & anElement)
//	: BaseArrayOfBF(count, anElement)
//	{
//		//!! NOTHING
//	}
//
//	ArrayOfBF(const BaseVector & aVector)
//	: BaseArrayOfBF( aVector )
//	{
//		//!! NOTHING
//	}
//
//	ArrayOfBF(const ArrayOfBF & anArray, const_reference lastValue)
//	: BaseArrayOfBF( anArray , lastValue)
//	{
//		//!! NOTHING
//	}
//
//
//	/**
//	 * DESTRUCTOR
//	 */
//	virtual ~ArrayOfBF()
//	{
//		BaseArrayOfBF::clear();
//	}
//
//
//	/**
//	 * SAVE
//	 */
//	inline void save( Element * anElement )
//	{
//		BaseArrayOfBF::append( BF( anElement) );
//	}
//
//
//	////////////////////////////////////////////////////////////////////////////
//	// raw iterator
//	////////////////////////////////////////////////////////////////////////////
//
//	template< class rawT >
//	class raw_iterator  :  public ArrayOfBF::iterator
//	{
//	public:
//		raw_iterator()
//		: ArrayOfBF::iterator( )
//		{
//			//!! NOTHING
//		}
//
//		raw_iterator(const ArrayOfBF::iterator & anIterator)
//		: ArrayOfBF::iterator( anIterator )
//		{
//			//!! NOTHING
//		}
//
//		inline operator rawT * () const
//		{
//			return( ArrayOfBF::iterator::_M_current->to_ptr< rawT >() );
//		}
//
//		inline rawT * operator->() const
//		{
//			return( ArrayOfBF::iterator::_M_current->to_ptr< rawT >() );
//		}
//
//	};
//
//
//	////////////////////////////////////////////////////////////////////////////
//	// const raw iterator
//	////////////////////////////////////////////////////////////////////////////
//
//	template< class rawT >
//	class const_raw_iterator  :  public ArrayOfBF::const_iterator
//	{
//	public:
//		const_raw_iterator()
//		: ArrayOfBF::const_iterator( )
//		{
//			//!! NOTHING
//		}
//
//		const_raw_iterator(const ArrayOfBF::const_iterator & anIterator)
//		: ArrayOfBF::const_iterator( anIterator )
//		{
//			//!! NOTHING
//		}
//
//		inline operator rawT * () const
//		{
//			return( ArrayOfBF::const_iterator::_M_current->to_ptr< rawT >() );
//		}
//
//		inline rawT * operator->() const
//		{
//			return( ArrayOfBF::const_iterator::_M_current->to_ptr< rawT >() );
//		}
//
//	};
//
//};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Vector of BF
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

class BFVector  :  public Vector < BF >
{

public:
	/**
	 * TYPEDEF
	 */
	typedef Vector < BF >    BaseVectorOfBF;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BFVector()
	: BaseVectorOfBF()
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BFVector(const BFVector & aVector)
	: BaseVectorOfBF( aVector )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Others
	 */
	explicit BFVector(avm_size_t count)
	: BaseVectorOfBF(count)
	{
		//!! NOTHING
	}

	explicit BFVector(avm_size_t count, const BF & elem)
	: BaseVectorOfBF(count, elem)
	{
		//!! NOTHING
	}

	explicit BFVector(const BF & arg)
	: BaseVectorOfBF( arg )
	{
		//!! NOTHING
	}

	explicit BFVector(const BF & arg1, const BF & arg2)
	: BaseVectorOfBF( arg1, arg2 )
	{
		//!! NOTHING
	}

	explicit BFVector(const BF & arg1, const BF & arg2, const BF & arg3)
	: BaseVectorOfBF( arg1, arg2, arg3 )
	{
		//!! NOTHING
	}

	explicit BFVector(const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4)
	: BaseVectorOfBF( arg1, arg2, arg3, arg4 )
	{
		//!! NOTHING
	}

	explicit BFVector(const BF & arg1, const BF & arg2,
			const BF & arg3, const BF & arg4, const BF & arg5)
	: BaseVectorOfBF( arg1, arg2, arg3, arg4, arg5 )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~BFVector()
	{
		BaseVectorOfBF::clear();
	}


	/**
	 * SAVE
	 */
	inline void save( Element * anElement )
	{
		BaseVectorOfBF::append( BF( anElement) );
	}


	////////////////////////////////////////////////////////////////////////////
	// raw iterator
	////////////////////////////////////////////////////////////////////////////

	template< class rawT >
	class raw_iterator  :  public BFVector::iterator
	{
	public:
		raw_iterator()
		: BFVector::iterator( )
		{
			//!! NOTHING
		}

		raw_iterator(const BFVector::iterator & anIterator)
		: BFVector::iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT * () const
		{
			return( BFVector::iterator::_M_current->to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			return( BFVector::iterator::_M_current->to_ptr< rawT >() );
		}

	};


	////////////////////////////////////////////////////////////////////////////
	// const raw iterator
	////////////////////////////////////////////////////////////////////////////

	template< class rawT >
	class const_raw_iterator  :  public BFVector::const_iterator
	{
	public:
		const_raw_iterator()
		: BFVector::const_iterator( )
		{
			//!! NOTHING
		}

		const_raw_iterator(const BFVector::const_iterator & anIterator)
		: BFVector::const_iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT * () const
		{
			return( BFVector::const_iterator::_M_current->to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			return( BFVector::const_iterator::_M_current->to_ptr< rawT >() );
		}

	};

};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Table of BF with raw_pointer using [ [ Fully ] Qualified ] Name ID - API
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

template< class BaseT >
class TableOfBF_T :
		public AvmObject ,
		public BFVector ,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfBF_T< BaseT > )
{

	AVM_DECLARE_CLONABLE_CLASS( TableOfBF_T )


public:
	/**
	 * TYPEDEF
	 */
	typedef  BaseT * PointerBaseT;

	typedef  BFVector::raw_iterator< BaseT > raw_iterator;

	typedef  BFVector::const_raw_iterator< BaseT > const_raw_iterator;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfBF_T()
	: AvmObject( ),
	BFVector( )
	{
		//!! NOTHING
	}

	TableOfBF_T(avm_size_t aSize)
	: AvmObject( ),
	BFVector( aSize )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfBF_T(const TableOfBF_T & aTable)
	: AvmObject( aTable ),
	BFVector( aTable )
	{
		//!! NOTHING
	}

	TableOfBF_T(const BFVector & aVector)
	: AvmObject( ),
	BFVector( aVector )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfBF_T()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * Element at <offset> position
	 */
	inline PointerBaseT rawAt(avm_size_t offset) const
	{
		return( BFVector::at(offset).template to_ptr< BaseT >() );
	}


	inline const BF & get(avm_size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset , BFVector::size() )
				<< "Unbound Element at <offset> position !!!"
				<< SEND_EXIT;

		return( BFVector::at(offset) );
	}


	/**
	 * GETTER
	 * Element by qlfNameID as QualifiedNameID w.r.t compare_op
	 */
	inline const BF & getByQualifiedNameID(
			const std::string & qlfNameID,
			NamedElement::op_comparer_t op) const
	{
		const_iterator it = begin();
		const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).to_ptr< BaseT >()->compare(qlfNameID, op) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByQualifiedNameID(
			const std::string & qlfNameID,
			NamedElement::op_comparer_t op) const
	{
		const_iterator it = begin();
		const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).to_ptr< BaseT >()->compareID(qlfNameID, op) )
			{
				return( (*it).to_ptr< BaseT >() );
			}
		}

		return( NULL );
	}


	/**
	 * GETTER
	 * Element by Fully Qualified NameID
	 */
	inline const BF & getByFQNameID(
			const std::string & aFullyQualifiedNameID) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			// STRICT:> compare LOCATOR & LOCATION (true:- retry only LOCATION)
			if( (it)->fqnEquals( aFullyQualifiedNameID , true ) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByFQNameID(
			const std::string & aFullyQualifiedNameID) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			// STRICT:> compare LOCATOR & LOCATION (true:- retry only LOCATION)
			if( (it)->fqnEquals( aFullyQualifiedNameID , true ) )
			{
				return( it );
			}
		}

		return( NULL );
	}


	/**
	 * GETTER
	 * Element by qlfNameID as QualifiedNameID
	 */
	inline const BF & getByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		const_iterator it = begin();
		const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).to_ptr< BaseT >()->fqnEndsWith(aQualifiedNameID) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		const_iterator it = begin();
		const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).to_ptr< BaseT >()->fqnEndsWith(aQualifiedNameID) )
			{
				return( (*it).to_ptr< BaseT >() );
			}
		}

		return( NULL );
	}


	inline avm_size_t getByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & listofFound) const
	{
		avm_size_t count = 0;

		const_iterator it = begin();
		const_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).to_ptr< BaseT >()->fqnEndsWith(aQualifiedNameID) )
			{
				listofFound.append( *it );

				++count;
			}
		}

		return( count );
	}


	/**
	 * GETTER
	 * Element by aNameID
	 */
	inline const BF & getByNameID(const std::string & aNameID) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (it)->getNameID() == aNameID )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByNameID(const std::string & aNameID) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (it)->getNameID() == aNameID )
			{
				return( it );
			}
		}

		return( NULL );
	}

	inline avm_size_t getByNameID(
			const std::string & aNameID, BFList & listofFound) const
	{
		avm_size_t count = 0;

		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (it)->getNameID() == aNameID )
			{
				listofFound.append( *it );

				++count;
			}
		}

		return( count );
	}


	inline avm_offset_t getOffsetByNameID(const std::string & aNameID) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( avm_offset_t offset = 0 ; it != endIt ; ++it , ++offset )
		{
			if( (it)->getNameID() == aNameID )
			{
				return( offset );
			}
		}
		return( AVM_NO_OFFSET );
	}


	/**
	 * GETTER
	 * Element by compiled form
	 */
	inline const BF & getByAstElement(const ObjectElement * astElement) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			if( (it)->isAstElement( astElement ) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}


	/**
	 * SAVE
	 * APPEND
	 */
	inline const BF & save(PointerBaseT anElement)
	{
		BFVector::push_back( BF(anElement) );

		return( BFVector::back() );
	}

	inline void append(const BF & anElement)
	{
		BFVector::append( anElement );
	}

	inline void append(const BFList & aList)
	{
		BFVector::append( aList );
	}

	inline void append(const BFVector & aVector)
	{
		BFVector::append( aVector );
	}


	/**
	 * SETTER
	 */
	inline void set(avm_offset_t offset, const BF & anElement)
	{
		BFVector::set(offset, anElement);
	}

	inline void set(avm_offset_t offset, PointerBaseT anElement)
	{
		BFVector::set(offset, BF(anElement));
	}


	/**
	 * contains a particular element
	 */
	inline bool contains(PointerBaseT anElement) const
	{
		if( (anElement->getOffset() < size()) &&
			(rawAt(anElement->getOffset()) == anElement) )
		{
			return( true );
		}
		else
		{
			const_raw_iterator it = BaseVector::begin();
			const_raw_iterator endIt = BaseVector::end();
			for( ; it != endIt ; ++it )
			{
				if( (it) == anElement )
				{
					return( true );
				}
			}

			return( false );
		}
	}


	inline bool contains(const BF & anElement) const
	{
		return( anElement.is< BaseT >()
				&& contains( anElement.to_ptr< BaseT >() ) );
	}


	/**
	 * Serialization
	 */
	inline virtual void strFQN(OutStream & os) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
//			os << TAB << str_fqn(it) << EOL;
			os << TAB << (it)->strFQN() << EOL;
		}
	}


	inline virtual void strHeader(OutStream & os) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
//			os << TAB << str_header( it ) << EOL;
			(it)->strHeader( os << TAB ); os << EOL;
		}
	}

	inline virtual void toStream(OutStream & os) const
	{
		const_raw_iterator it = begin();
		const_raw_iterator endIt = end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(os);
		}
	}

};


/**
 * operator <<
 */
AVM_OS_STREAM_COLLECTION( BFList     )
AVM_OS_STREAM_COLLECTION( ArrayOfBF  )
AVM_OS_STREAM_COLLECTION( BFVector   )
AVM_OS_STREAM_COLLECTION( BFMultiset )
AVM_OS_STREAM_COLLECTION( BFSet      )



typedef  List < BFList * > ListOfBFList;


} /* namespace sep */

#endif /* BFCONTAINER_H_ */
