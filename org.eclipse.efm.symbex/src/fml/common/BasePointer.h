/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef BASEPOINTER_H_
#define BASEPOINTER_H_

#include <common/BF.h>


namespace sep
{

class Modifier;
class ObjectElement;


template< class ClassT  >
class BasePointer :
//		public AvmPointer< ClassT , DestroyElementPolicy >,
		public BF

{

private:
	/**
	 * TYPEDEF
	 */
//	typedef  AvmPointer< ClassT , DestroyElementPolicy >  base_this_type;
	typedef  BF  base_this_type;

protected:
	typedef       ClassT    value_type;

	typedef       ClassT &  reference;
	typedef const ClassT &  const_reference;


	typedef       ClassT *  pointer;
	typedef const ClassT *  const_pointer;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	BasePointer()
	: base_this_type( )
	{
		//!!! NOTHING
	}

	explicit BasePointer(pointer ptr)
	: base_this_type( ptr )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	BasePointer(const BasePointer & aPointer)
	: base_this_type( aPointer )
	{
		//!! NOTHING
	}

	explicit BasePointer(const BF & aPointer)
	: base_this_type( aPointer )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~BasePointer()
	{
		//!!! NOTHING
	}


protected:
	inline pointer raw_pointer() const
	{
		return( mPTR  );
	}

	inline pointer ptrBase() const
	{
		return( static_cast< pointer >( mPTR ) );
	}


protected:
	////////////////////////////////////////////////////////////////////////////
	// TYPE CAST
	////////////////////////////////////////////////////////////////////////////

	// cast BF as specified pointer
	template< class T >
	inline T * as_ptr() const
	{
		// previous:> AVM_OS_ASSERT_WARNING_ALERT
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BasePointer::as_ptr< T >() !!!"
				<< SEND_EXIT;

		return( (mPTR != NULL) ? mPTR->as< T >() : NULL );
	}

	template< class T >
	inline T * to_ptr() const
	{
		return( mPTR->to< T >() );
	}


	// cast BF as specified reference
	template< class T >
	inline T & as_ref()
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BasePointer::as_ref< T >() !!!"
				<< SEND_EXIT;

		return( *( mPTR->as< T >() ) );
	}

	template< class T >
	inline const T & as_ref() const
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( mPTR )
				<< "raw_pointer in BasePointer::as_ref< T >() !!!"
				<< SEND_EXIT;

		return( *( mPTR->as< T >() ) );
	}


	// cast BF as derived BF
	template< class T >
	inline T & as_bf()
	{
		return( static_cast< T & >( *this ) );
	}

	template< class T >
	inline const T & as_bf() const
	{
		return( static_cast< const T & >( *this ) );
	}



protected:
	/**
	 * CAST
	 */
	inline operator pointer () const
	{
		return( ptrBase() );
	}

	/**
	 * OPERATORS
	 */
	inline pointer operator-> () const
	{
		return( ptrBase() );
	}


public:
	/**
	 * ASSIGNMENT
	 * BF
	 */

	inline bool operator==(const_pointer aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	inline bool operator==(pointer aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	inline bool operator==(const BasePointer & other) const
	{
		return( base_this_type::mPTR == other.mPTR );
	}


	inline bool operator!=(const_pointer aPtr) const
	{
		return( base_this_type::mPTR != aPtr );
	}

	inline bool operator!=(const BasePointer & other) const
	{
		return( base_this_type::mPTR != other.mPTR );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// BaseCompiledForm
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER
	 * modifier of a USER FORM
	 */
	inline virtual const Modifier & getModifier() const
	{
		return( ptrBase()->getModifier() );
	}

	inline virtual Modifier & getwModifier()
	{
		return( ptrBase()->getwModifier() );
	}


	/**
	 * GETTER - SETTER
	 * theCompiledForm
	 */
	inline const ObjectElement * getAstElement() const
	{
		return( ptrBase()->getAstElement() );
	}

	inline bool isAstElement(const ObjectElement * astElement) const
	{
		return( ptrBase()->isAstElement( astElement ) );
	}

	inline bool hasAstElement() const
	{
		return( ptrBase()->hasAstElement() );
	}

	inline std::string getAstFullyQualifiedNameID() const
	{
		return( ptrBase()->getAstFullyQualifiedNameID() );
	}

	inline std::string getAstNameID() const
	{
		return( ptrBase()->getAstNameID() );
	}

	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline std::string getFullyQualifiedNameID() const
	{
		return( ptrBase()->getFullyQualifiedNameID() );
	}

	inline bool hasFullyQualifiedNameID() const
	{
		return( ptrBase()->hasFullyQualifiedNameID() );
	}

	inline void setFullyQualifiedNameID(const std::string & aFQN_ID)
	{
		ptrBase()->setFullyQualifiedNameID( aFQN_ID );
	}

	inline void updateFullyQualifiedNameID()
	{
		ptrBase()->updateFullyQualifiedNameID();
	}

	inline bool fqnEquals(const std::string & aFullyQualifiedNameID,
			bool enabledOnlyLocationComparisonElse = false) const
	{
		return( ptrBase()->fqnEquals(aFullyQualifiedNameID,
				enabledOnlyLocationComparisonElse) );
	}

	inline bool fqnEndsWith(const std::string & aQualifiedNameID) const
	{
		return( ptrBase()->fqnEndsWith(aQualifiedNameID) );
	}

	/**
	 * GETTER - SETTER
	 * theId
	 */
	inline std::string getNameID() const
	{
		return( ptrBase()->getNameID() );
	}

	inline bool hasNameID() const
	{
		return( ptrBase()->hasNameID() );
	}

	inline void setNameID(const std::string & aNameID)
	{
		ptrBase()->setNameID( aNameID );
	}

	void updateNameID()
	{
		ptrBase()->updateNameID();
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	{
		ptrBase()->setAllNameID( aFullyQualifiedNameID , aNameID );
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & name)
	{
		ptrBase()->setAllNameID( aFullyQualifiedNameID , aNameID , name );
	}

};



} /* namespace sep */

#endif /* BASEPOINTER_H_ */
