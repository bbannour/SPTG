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
#include <common/BF.h>
#include <common/NamedElement.h>

#include <collection/Collection.h>
#include <collection/Array.h>
#include <collection/List.h>
#include <collection/Multiset.h>
#include <collection/Set.h>
#include <collection/Vector.h>

#include <fml/common/ObjectElement.h>


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
	// const raw iterator
	////////////////////////////////////////////////////////////////////////////

	template< class rawT >
	class const_ref_iterator  :  public BFList::const_iterator
	{
	public:
		const_ref_iterator()
		: BFList::const_iterator( )
		{
			//!! NOTHING
		}

		const_ref_iterator(const BFList::const_iterator & anIterator)
		: BFList::const_iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT const & () const
		{
			const BF & current = BFList::const_iterator::operator*();

			return( current.to< rawT >() );
		}

		inline rawT * operator->() const
		{
			const BF & current = BFList::const_iterator::operator*();

			return( current.to_ptr< rawT >() );
		}

	};


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
//	explicit ArrayOfBF(std::size_t count)
//	: BaseArrayOfBF(count)
//	{
//		//!! NOTHING
//	}
//
//	explicit ArrayOfBF(std::size_t count, const BF & anElement)
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
//			return( ArrayOfBF::iterator::base()->to_ptr< rawT >() );
//		}
//
//		inline rawT * operator->() const
//		{
//			return( ArrayOfBF::iterator::base()->to_ptr< rawT >() );
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
//			return( ArrayOfBF::const_iterator::base()->to_ptr< rawT >() );
//		}
//
//		inline rawT * operator->() const
//		{
//			return( ArrayOfBF::const_iterator::base()->to_ptr< rawT >() );
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
	explicit BFVector(std::size_t count)
	: BaseVectorOfBF(count)
	{
		//!! NOTHING
	}

	explicit BFVector(std::size_t count, const BF & elem)
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
	// ref iterator
	////////////////////////////////////////////////////////////////////////////

	template< class refT >
	class ref_iterator  :  public BFVector::iterator
	{
	public:
		ref_iterator()
		: BFVector::iterator( )
		{
			//!! NOTHING
		}

		ref_iterator(const BFVector::iterator & anIterator)
		: BFVector::iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator refT & () const
		{
			return( BFVector::iterator::base()->template to< refT >() );
		}

		inline operator refT * () const
		{
			return( BFVector::iterator::base()->template to_ptr< refT >() );
		}

		inline refT * operator->() const
		{
			return( BFVector::iterator::base()->template to_ptr< refT >() );
		}

	};


	////////////////////////////////////////////////////////////////////////////
	// const ref iterator
	////////////////////////////////////////////////////////////////////////////

	template< class refT >
	class const_ref_iterator  :  public BFVector::const_iterator
	{
	public:
		const_ref_iterator()
		: BFVector::const_iterator( )
		{
			//!! NOTHING
		}

		const_ref_iterator(const BFVector::const_iterator & anIterator)
		: BFVector::const_iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator refT const & () const
		{
			return( BFVector::const_iterator::base()->template to< refT >() );
		}

		inline operator refT const * () const
		{
			return( BFVector::const_iterator::base()->template to_ptr< refT >() );
		}

		inline refT * operator->() const
		{
			return( BFVector::const_iterator::base()->template to_ptr< refT >() );
		}

	};


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
			return( BFVector::iterator::base()->template to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			return( BFVector::iterator::base()->template to_ptr< rawT >() );
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

		const_raw_iterator(const BFVector::iterator & anIterator)
		: BFVector::const_iterator( anIterator )
		{
			//!! NOTHING
		}

		inline operator rawT * () const
		{
			return( BFVector::const_iterator::base()->template to_ptr< rawT >() );
		}

		inline rawT * operator->() const
		{
			return( BFVector::const_iterator::base()->template to_ptr< rawT >() );
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

	AVM_DECLARE_CLONABLE_BASE_CLASS( TableOfBF_T )


public:
	/**
	 * TYPEDEF
	 */
	typedef  BaseT * PointerBaseT;

	typedef  BaseT   ReferenceBaseT;

	typedef  BFVector::ref_iterator< BaseT > ref_iterator;

	typedef  BFVector::raw_iterator< BaseT > raw_iterator;

	typedef  BFVector::const_ref_iterator< BaseT > const_ref_iterator;

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

	TableOfBF_T(std::size_t aSize)
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
	inline const ReferenceBaseT & refAt(std::size_t offset) const
	{
		return( BFVector::at(offset).template to< BaseT >() );
	}

	inline ReferenceBaseT & refAt(std::size_t offset)
	{
		return( BFVector::at(offset).template to< BaseT >() );
	}



	inline PointerBaseT rawAt(std::size_t offset) const
	{
		return( BFVector::at(offset).template to_ptr< BaseT >() );
	}

	inline const BF & get(std::size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset , BFVector::size() )
				<< "Unbound Element at <offset> position !!!"
				<< SEND_EXIT;

		return( BFVector::at(offset) );
	}

	/**
	 * GETTER
	 * Element by its raw pointer
	 */
//	inline const BF & get(PointerBaseT anElement) const
//	{
//		if( anElement != nullptr )
//		{
//			if( (anElement->getOwnedOffset() < size())
//				&& (rawAt(anElement->getOwnedOffset()) == anElement) )
//			{
//				return( BFVector::at(anElement->getOwnedOffset()) );
//			}
//			else if( (anElement->getRuntimeOffset() < size())
//				&& (rawAt(anElement->getRuntimeOffset()) == anElement) )
//			{
//				return( BFVector::at(anElement->getRuntimeOffset()) );
//			}
//			else
//			{
//				const_raw_iterator it = BaseVector::begin();
//				const_raw_iterator endIt = BaseVector::end();
//				for( ; it != endIt ; ++it )
//				{
//					if( (it) == anElement )
//					{
//						return( *it );
//					}
//				}
//			}
//		}
//
//		return( BF::REF_NULL );
//	}


	/**
	 * GETTER
	 * Element by aQualifiedNameID as QualifiedNameID w.r.t compare_op
	 */
	inline const BF & getByQualifiedNameID(
			const std::string & aQualifiedNameID,
			NamedElement::op_comparer_t op) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->compare(aQualifiedNameID, op) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByQualifiedNameID(
			const std::string & aQualifiedNameID,
			NamedElement::op_comparer_t op) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->isEqualsID(aQualifiedNameID, op) )
			{
				return( it );
			}
		}

		return( nullptr );
	}


	/**
	 * GETTER
	 * Element by Fully Qualified NameID
	 */
	inline const BF & getByFQNameID(
			const std::string & aFullyQualifiedNameID,
			bool enabledOnlyLocationComparisonElse = true) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			// STRICT:> compare LOCATOR & LOCATION (true:- retry only LOCATION)
			if( (it)->fqnEquals( aFullyQualifiedNameID,
					enabledOnlyLocationComparisonElse ) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByFQNameID(
			const std::string & aFullyQualifiedNameID) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			// STRICT:> compare LOCATOR & LOCATION (true:- retry only LOCATION)
			if( (it)->fqnEquals( aFullyQualifiedNameID , true ) )
			{
				return( it );
			}
		}

		return( nullptr );
	}


	/**
	 * GETTER
	 * Element by anID
	 */
	inline const BF & getByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( getByNameID( anID ) );
		}
		else
		{
			return( getByQualifiedNameID( anID ) );
		}
	}

	inline PointerBaseT rawByID(const std::string & anID) const
	{
		if( anID.find('.') == std::string::npos )
		{
			return( rawByNameID( anID ) );
		}
		else
		{
			return( rawByQualifiedNameID( anID ) );
		}
	}


	/**
	 * GETTER
	 * Element by aQualifiedNameID as QualifiedNameID
	 */
	inline const BF & getByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->fqnEndsWith(aQualifiedNameID) )
			{
				return( *it );
			}
		}

		return( BF::REF_NULL );
	}

	inline PointerBaseT rawByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->fqnEndsWith(aQualifiedNameID) )
			{
				return( it );
			}
		}

		return( nullptr );
	}


	inline std::size_t getByQualifiedNameID(
			const std::string & aQualifiedNameID, BFList & listofFound) const
	{
		std::size_t count = 0;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->fqnEndsWith(aQualifiedNameID) )
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
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
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
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->getNameID() == aNameID )
			{
				return( it );
			}
		}

		return( nullptr );
	}

	inline std::size_t getByNameID(
			const std::string & aNameID, BFList & listofFound) const
	{
		std::size_t count = 0;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
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


	inline std::list< std::string> getListOfAllNameID() const
	{
		std::list< std::string> allNameID;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			allNameID.push_back( (it)->getNameID() );
		}

		return allNameID;
	}

	inline std::vector< std::string> getVectorOfAllNameID() const
	{
		std::vector< std::string> allNameID;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			allNameID.push_back( (it)->getNameID() );
		}

		return allNameID;
	}


	/**
	 * GETTER
	 * Element by aREGEX
	 */
	inline std::size_t getByQualifiedNameREGEX(
			const std::string & aREGEX, BFList & listofFound) const
	{
		std::size_t count = 0;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->fqnRegexMatch(aREGEX) )
			{
				listofFound.append( *it );

				++count;
			}
		}

		return( count );
	}

	inline std::size_t getByNameREGEX(
			const std::string & aREGEX, BFList & listofFound) const
	{
		std::size_t count = 0;

		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->nameRegexMatch(aREGEX) )
			{
				listofFound.append( *it );

				++count;
			}
		}

		return( count );
	}



	/**
	 * GETTER
	 * Element by compiled form
	 */
	inline const BF & getByAstElement(const ObjectElement & astElement) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
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

	inline void append(const BF & anElement) override
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

	// Due to [-Woverloaded-virtual=]
	using BFVector::append;


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
	inline bool contains(const ObjectElement * anElement) const
	{
		if( (anElement->getRuntimeOffset() < size())
			&& (rawAt(anElement->getRuntimeOffset()) == anElement) )
		{
			return( true );
		}
		else if( (anElement->getOwnedOffset() < size())
			&& (rawAt(anElement->getOwnedOffset()) == anElement) )
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


	inline bool contains(const BF & anElement) const override
	{
		return( anElement.is< BaseT >()
				&& contains( anElement.to_ptr< BaseT >() ) );
	}

	using BFVector::contains;


	/**
	 * REMOVE
	 * Element by aNameID
	 */
	inline void removeByNameID(const std::string & aNameID)
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			if( (it)->getNameID() == aNameID )
			{
				BaseVector::erase(it);
				break;
			}
		}
	}


	/**
	 * Serialization
	 */
	inline void strFQN(OutStream & os) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
//			os << TAB << str_fqn(it) << EOL;
			os << TAB << (it)->strFQN() << EOL;
		}
	}


	inline void strHeader(OutStream & os) const
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
//			os << TAB << str_header( it ) << EOL;
			(it)->strHeader( os << TAB ); os << EOL;
		}
	}

	inline virtual void toStream(OutStream & os) const override
	{
		const_raw_iterator endIt = end();
		for( const_raw_iterator it = begin() ; it != endIt ; ++it )
		{
			(it)->toStream(os);
		}
	}

	// Due to [-Woverloaded-virtual=]
	using AvmObject::toStream;

};

////////////////////////////////////////////////////////////////////////////////
// MACRO FOR TYPEDEF DEFINITION
////////////////////////////////////////////////////////////////////////////////


#define AVM_TYPEDEF_TABLE_CLASS(ClassName)   \
public:                                      \
	typedef TableOfBF_T< ClassName > Table;  \
private:


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
