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
	typedef       ClassT    value_t;

	typedef       ClassT &  reference_t;
	typedef const ClassT &  const_reference_t;


	typedef       ClassT *  pointer_t;
	typedef const ClassT *  const_pointer_t;


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

	explicit BasePointer(pointer_t ptr)
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
	inline pointer_t raw_pointer() const
	{
		return( static_cast< pointer_t >( mPTR ) );
	}


protected:
	/**
	 * OPERATORS
	 */
	inline pointer_t operator-> () const
	{
		return( raw_pointer() );
	}

public:
	/**
	 * ASSIGNMENT
	 * BF
	 */

	inline bool operator==(const_reference_t aRef) const
	{
		return( base_this_type::mPTR == (& aRef) );
	}

	inline bool operator==(const_pointer_t aPtr) const
	{
		return( base_this_type::mPTR == aPtr );
	}

	inline bool operator==(const BasePointer & other) const
	{
		return( base_this_type::mPTR == other.mPTR );
	}


	inline bool operator!=(const_reference_t aRef) const
	{
		return( base_this_type::mPTR != (& aRef) );
	}

	inline bool operator!=(const_pointer_t aPtr) const
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
		return( raw_pointer()->getModifier() );
	}

	inline virtual Modifier & getwModifier()
	{
		return( raw_pointer()->getwModifier() );
	}


	/**
	 * GETTER - SETTER
	 * theCompiledForm
	 */
	inline const ObjectElement & getAstElement() const
	{
		return( raw_pointer()->getAstElement() );
	}

	inline const ObjectElement & safeAstElement() const
	{
		return( raw_pointer()->safeAstElement() );
	}

	inline bool isAstElement(const ObjectElement & astElement) const
	{
		return( raw_pointer()->isAstElement( astElement ) );
	}

	inline bool hasAstElement() const
	{
		return( raw_pointer()->hasAstElement() );
	}

	inline std::string getAstFullyQualifiedNameID() const
	{
		return( raw_pointer()->getAstFullyQualifiedNameID() );
	}

	inline std::string getAstNameID() const
	{
		return( raw_pointer()->getAstNameID() );
	}

	/**
	 * GETTER - SETTER
	 * mFullyQualifiedNameID
	 */
	inline std::string getFullyQualifiedNameID() const
	{
		return( raw_pointer()->getFullyQualifiedNameID() );
	}

	inline bool hasFullyQualifiedNameID() const
	{
		return( raw_pointer()->hasFullyQualifiedNameID() );
	}

	inline void setFullyQualifiedNameID(const std::string & aFQN_ID)
	{
		raw_pointer()->setFullyQualifiedNameID( aFQN_ID );
	}

	inline void updateFullyQualifiedNameID()
	{
		raw_pointer()->updateFullyQualifiedNameID();
	}

	inline bool fqnEquals(const std::string & aFullyQualifiedNameID,
			bool enabledOnlyLocationComparisonElse = false) const
	{
		return( raw_pointer()->fqnEquals(aFullyQualifiedNameID,
				enabledOnlyLocationComparisonElse) );
	}

	inline bool fqnEndsWith(const std::string & aQualifiedNameID) const
	{
		return( raw_pointer()->fqnEndsWith(aQualifiedNameID) );
	}

	inline bool fqnRegexMatch(const std::string & aRegex) const
	{
		return( raw_pointer()->fqnRegexMatch(aRegex) );
	}


	/**
	 * GETTER - SETTER
	 * theId
	 */
	inline std::string getNameID() const
	{
		return( raw_pointer()->getNameID() );
	}

	inline bool nameRegexMatch(const std::string & aRegex) const
	{
		return( raw_pointer()->nameRegexMatch(aRegex) );
	}

	inline bool hasNameID() const
	{
		return( raw_pointer()->hasNameID() );
	}

	inline void setNameID(const std::string & aNameID)
	{
		raw_pointer()->setNameID( aNameID );
	}

	void updateNameID()
	{
		raw_pointer()->updateNameID();
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID)
	{
		raw_pointer()->setAllNameID( aFullyQualifiedNameID , aNameID );
	}

	inline void setAllNameID(const std::string & aFullyQualifiedNameID,
			const std::string & aNameID, const std::string & name)
	{
		raw_pointer()->setAllNameID( aFullyQualifiedNameID , aNameID , name );
	}

};



} /* namespace sep */

#endif /* BASEPOINTER_H_ */
