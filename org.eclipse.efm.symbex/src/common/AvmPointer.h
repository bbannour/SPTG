/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 févr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMPOINTER_H_
#define AVMPOINTER_H_

#include <base/SmartPointer.h>


#include <common/BF.h>

#include <printer/OutStream.h>


namespace sep
{


template< class T , class Tdestructor >
class AvmPointer  :  public SmartPointer< T , Tdestructor >
{

private:
	/**
	 * TYPEDEF
	 */
	typedef       SmartPointer< T , Tdestructor >  base_this_type;
	typedef            AvmPointer< T , Tdestructor >  this_type;

protected:
	typedef       T    value_type;

	typedef       T &  reference;
	typedef const T &  const_reference;


	typedef       T *  pointer;
	typedef const T *  const_pointer;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmPointer()
	: base_this_type( )
	{
		//!!! NOTHING
	}

	explicit AvmPointer(pointer ptr)
	: base_this_type( ptr )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	AvmPointer(const AvmPointer & other)
	: base_this_type( other )
	{
		//!!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmPointer()
	{
		//!!! NOTHING
	}


	/**
	 * CAST
	 */
	inline operator pointer () const
	{
		return( base_this_type::mPTR );
	}

	// Desactive call of << delete >> using compiler ambiguous mecanism
	inline operator void * () const
	{
		return( this_type::raw_pointer() );
	}


	/**
	 * OPERATORS
	 */
	inline pointer operator-> () const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( base_this_type::mPTR )
				<< "raw_pointer in AvmPointer !!!"
				<< SEND_EXIT;

		return( base_this_type::mPTR );
	}


	/**
	 * ASSIGNMENT
	 */
	inline AvmPointer & operator=(pointer aPtr)
	{
		if( base_this_type::mPTR != aPtr )
		{
			base_this_type::release( aPtr );
		}
		return( *this );
	}

	inline AvmPointer & operator=(const AvmPointer & other)
	{
		if( base_this_type::mPTR != other.mPTR )
		{
			base_this_type::release_acquire( other.mPTR );
		}
		return( *this );
	}


	inline AvmPointer & operator=(const BF & other)
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( other.is_weakly< value_type >() )
				<< "Invalid Assignment Cast of a BF to a "
					"AvmPointer< T , Tdestructor > !!!"
				<< SEND_EXIT;

		if( base_this_type::mPTR != other.raw_pointer() )
		{
			base_this_type::release_acquire( const_cast<pointer>(
					static_cast< pointer >(other.raw_pointer()) ) );
		}
		return( *this );
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline bool operator==(const_pointer aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	template< class U >
	inline bool operator==(const U * aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	inline bool operator==(const AvmPointer & other) const
	{
		return( base_this_type::mPTR == other.mPTR );
	}

	inline bool operator==(const BF & other) const
	{
		return( base_this_type::mPTR == other.raw_pointer() );
	}


	inline bool operator!=(const_pointer aPtr) const
	{
		return( base_this_type::mPTR != aPtr );
	}

	template< class U >
	inline bool operator!=(const U * aPtr) const
	{
		return( base_this_type::mPTR != aPtr );
	}

	inline bool operator!=(const AvmPointer & other) const
	{
		return( base_this_type::mPTR != other.mPTR );
	}

	inline bool operator!=(const BF & other) const
	{
		return( base_this_type::mPTR != other.raw_pointer() );
	}



	/**
	 * COMPARISON
	 */
	inline bool isEQ(const_pointer aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	inline bool isEQ(const AvmPointer & other) const
	{
		return( base_this_type::mPTR == other.mPTR );
	}


	inline bool isNEQ(const_pointer aPtr) const
	{
		return( base_this_type::mPTR != aPtr );
	}

	inline bool isNEQ(const AvmPointer & other) const
	{
		return( base_this_type::mPTR != other.mPTR );
	}


	/**
	 * Serialization
	 */
	inline void toStream(OutStream & os) const
	{
		if( base_this_type::mPTR != NULL )
		{
			base_this_type::mPTR->toStream(os);
		}
		else
		{
			os << TAB << "AvmPointer<null>" << EOL_FLUSH;
		}
	}


	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const
	{
		StringOutStream oss(indent);

		toStream(oss);

		return( oss.str() );
	}


	/**
	 * DEFAULT NULL
	 */
	static AvmPointer  REF_NULL;

};


template< class T , class Tdestructor >
AvmPointer< T , Tdestructor >  AvmPointer< T , Tdestructor >::REF_NULL;


#define AP_REF_NULL(ClassName)  AP##ClassName::REF_NULL


#define AVM_DEFINE_AP_CLASS(ClassName)   \
		typedef AvmPointer< ClassName , DestroyObjectPolicy > AP##ClassName;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#define INCR_BF(A)   \
		sep::BF( sep::incrReferenceCount(A) )


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// TYPE DEFINITION for SMART POINTER.
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


//template< class T >
//class AvmCloneableClass
//{
//
//public:
//	/**
//	 * DESTRUCTOR
//	 */
//	virtual ~AvmCloneableClass()
//	{
//		//!! NOTHING
//	}
//
//	virtual T * clone() const
//	{
//		return( new T(*this) );
//	}
//};


#define AVM_DECLARE_CLONABLE_CLASS(ClassName)  \
public:                                        \
	virtual ClassName * clone() const          \
	{ return( new ClassName(*this) ); }        \
private:



//template< class T >
//class AvmUncloneableClass
//{
//
//public:
//	/**
//	 * DESTRUCTOR
//	 */
//	virtual ~AvmUncloneableClass()
//	{
//		//!! NOTHING
//	}
//
//	virtual T * clone() const
//	{
//		return( const_cast< T * >(this) );
//	}
//};


#define AVM_DECLARE_UNCLONABLE_CLASS(ClassName)     \
public:                                             \
	virtual ClassName * clone() const               \
	{ return( const_cast< ClassName * >(this) ); }  \
private:


} /* namespace sep */
#endif /* AVMPOINTER_H_ */
