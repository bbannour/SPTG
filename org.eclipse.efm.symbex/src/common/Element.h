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
#ifndef COMMON_ELEMENT_H_
#define COMMON_ELEMENT_H_

#include <base/ClassKindInfo.h>
#include <common/AvmObject.h>

namespace sep
{


class BF;


class Element :
		public AvmObject,
		public ClassKindImpl,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( Element )
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Element(class_kind_t aClassKind)
	: AvmObject( ),
	ClassKindImpl( aClassKind )
	{
			//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 * Abstract pur
	 */
	Element(const Element & anElement)
	: AvmObject( anElement ),
	ClassKindImpl( anElement )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~Element()
	{
		//!! NOTHING
	}


	inline std::intptr_t raw_address() const
	{
		return( std::intptr_t( this ) );
	}


	/**
	 * CLONE
	 */
	virtual Element * clone() const = 0;


	/**
	 * GETTER - SETTER
	 * for container of BF
	 */
	// Generally with range check
	virtual BF & at(std::size_t offset);
	virtual const BF & at(std::size_t offset) const;

	// Generally with range check
	virtual const BF & operator[](std::size_t offset) const;
	virtual BF & operator[](std::size_t offset);

	virtual BF & getWritable(std::size_t offset);

	virtual void makeWritable(std::size_t offset);

	virtual void set(std::size_t offset, const BF & bf);

	virtual std::size_t size() const;


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline virtual bool isEQ(const Element & anElement) const
	{
		return( this == (& anElement) );
	}

	inline virtual bool isEQ(const Element * anElement) const
	{
		return( (anElement != nullptr) && isEQ(* anElement) );
	}


	inline virtual bool isNEQ(const Element & anElement) const
	{
		return( this != (& anElement) );
	}

	inline virtual bool isNEQ(const Element * anElement) const
	{
		return( (anElement == nullptr) || isNEQ(* anElement) );
	}


	virtual bool isTEQ(const Element & anElement) const
	{
		return( this == (& anElement) );
	}

	virtual bool isTEQ(const Element * anElement) const
	{
		return( this == anElement );
	}


	inline virtual bool isNTEQ(const Element & anElement) const
	{
		return( this != (& anElement) );
	}

	inline virtual bool isNTEQ(const Element * anElement) const
	{
		return( this != anElement );
	}


	/**
	 * SERIALIZATION
	 */
	virtual void toStream(OutStream & os) const override = 0;


	inline void toFscn(OutStream & os) const
	{
		toStream( os );
	}

	inline void serialize(OutStream & os) const
	{
		toStream( os );
	}

	inline virtual std::string str() const
	{
		StringOutStream oss( AVM_STR_INDENT );

		toStream( oss << IGNORE_FIRST_TAB );

		return( oss.str() );
	}


	inline virtual std::string strNum(
			uint8_t precision = AVM_MUMERIC_PRECISION) const
	{
		return( str() );
	}


	/**
	 * TRACE on DESTROY
	 * dbgDestroy
	 */
	inline void dbgDestroy() const
	{
		AVM_OS_WARN << "destroy< @ " << std::intptr_t( this )
				<< " , " << std::setw(16) << classKindName() << " > : "
				<< std::flush << str() << std::endl;
	}

};



////////////////////////////////////////////////////////////////////////////////
//// DESTROY POLICY for SMART POINTER.
////////////////////////////////////////////////////////////////////////////////

struct DestroyElementPolicy
{
	static void destroy(Element * anObject);
};

inline void destroyElement(Element * anElement)
{
	DestroyElementPolicy::destroy(anElement);
}



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//// TYPE DEFINITION for SMART POINTER.
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


#define AVM_DECLARE_CLONABLE_BASE_CLASS(ClassName)  \
public:                                             \
	virtual ClassName * clone() const               \
	{ return( new ClassName(*this) ); }             \
private:


#define AVM_DECLARE_CLONABLE_CLASS(ClassName)       \
public:                                             \
	virtual ClassName * clone() const override      \
	{ return( new ClassName(*this) ); }             \
private:


template< class T >
class ClonableElement :  public Element
{

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ClonableElement(class_kind_t aClassKind)
	: Element( aClassKind )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	ClonableElement(const Element & anElement)
	: Element( anElement )
	{
		//!! NOTHING
	}


	/**
	 * CLONE
	 */
	virtual T * clone() const
	{
		return( new T( * static_cast< const T * >(this) ) );
	}
};




#define AVM_DECLARE_UNCLONABLE_CLASS(ClassName)     \
public:                                             \
	virtual ClassName * clone() const override      \
	{ return( const_cast< ClassName * >(this) ); }  \
private:


template< class T >
class UnclonableElement :  public Element
{

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	UnclonableElement(class_kind_t aClassKind)
	: Element( aClassKind )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	UnclonableElement(const Element & anElement)
	: Element( anElement )
	{
		//!! NOTHING
	}


	/**
	 * CLONE
	 */
	virtual T * clone() const
	{
		return( const_cast< T * >(this) );
	}
};


}

#endif /*COMMON_ELEMENT_H_*/
