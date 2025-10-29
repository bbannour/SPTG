/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TYPESPECIFIER_H_
#define TYPESPECIFIER_H_

#include <fml/common/BasePointer.h>

#include <fml/lib/ITypeSpecifier.h>

#include <fml/type/BaseTypeSpecifier.h>



#define AVM_DEBUG_TYPE_POINTER  true
#undef AVM_DEBUG_TYPE_POINTER

#if defined(AVM_DEBUG_TYPE_POINTER)

	#define AVM_DECLARE_DEBUG_TYPE_PTR      const BaseTypeSpecifier * debugPTR;

	#define AVM_INIT_DEBUG_TYPE_PTR( ptr )  , debugPTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_TYPE_PTR( ptr )  debugPTR = ptr;

	#define AVM_ASSIGN_EXPR_DEBUG_TYPE_PTR( ptr )   debugPTR = ptr

#else

	#define AVM_DECLARE_DEBUG_TYPE_PTR

	#define AVM_INIT_DEBUG_TYPE_PTR( ptr )

	#define AVM_ASSIGN_STMNT_DEBUG_TYPE_PTR( ptr )

	#define AVM_ASSIGN_EXPR_DEBUG_TYPE_PTR( ptr )  ptr

#endif




namespace sep
{


class BF;

class BaseSymbolTypeSpecifier;

class ClassTypeSpecifier;
class ContainerTypeSpecifier;
class EnumTypeSpecifier;
class IntervalTypeSpecifier;
class TypeAliasSpecifier;
class UnionTypeSpecifier;

class InstanceOfData;

class Symbol;
class TableOfSymbol;


class TypeSpecifier final :
		public BasePointer< BaseTypeSpecifier >,
		public ITypeSpecifier,
		AVM_INJECT_STATIC_NULL_REFERENCE( TypeSpecifier ),
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TypeSpecifier )
{

private:
	/**
	 * TYPEDEF
	 */
	typedef  BasePointer< BaseTypeSpecifier >  base_this_type;



public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TypeSpecifier()
	: base_this_type( )
	{
		//!!! NOTHING
	}

	explicit TypeSpecifier(BaseTypeSpecifier * anInstance)
	: base_this_type( anInstance )
	{
		//!!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TypeSpecifier(const TypeSpecifier & aType)
	: base_this_type( aType )
	{
		//!! NOTHING
	}

	explicit TypeSpecifier(const BF & aType)
	: base_this_type( aType )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~TypeSpecifier()
	{
		//!!! NOTHING
	}

	/**
	 * GETTER
	 * Unique Null Reference
	 */
	inline static TypeSpecifier & nullref()
	{
		static 	TypeSpecifier _NULL_;

		return( _NULL_ );
	}


	/**
	 * GETTER
	 * pointer
	 */
	inline operator pointer_t () const
	{
		return( static_cast< pointer_t >( mPTR ) );
	}

	inline const_pointer_t rawType() const
	{
		return( static_cast< const_pointer_t >( mPTR ) );
	}


	inline operator const_reference_t () const
	{
		return( static_cast< const_reference_t >( *mPTR ) );
	}

	inline const_reference_t refType() const
	{
		return( static_cast< const_reference_t & >( *mPTR ) );
	}

	inline reference_t refType()
	{
		return( static_cast< reference_t & >( *mPTR ) );
	}


public:

	/**
	 * ASSIGNMENT
	 * BF
	 */
	TypeSpecifier & operator=(const BF & aType);

	inline TypeSpecifier & operator=(pointer_t aPtr)
	{
		if( mPTR != aPtr )
		{
			AVM_ASSIGN_DEBUG_BF_PTR( aPtr )

			release( aPtr );
		}
		return( *this );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// BaseTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	/**
	 * GETTER - SETTER
	 * theTypeSpecifier
	 */
	inline virtual const BaseTypeSpecifier & thisTypeSpecifier() const override
	{
		return( refType() );
	}

	inline const BaseTypeSpecifier & getTypeSpecifier() const
	{
		return( refType() );
	}


	inline virtual avm_type_specifier_kind_t getTypeSpecifierKind() const override
	{
		return( refType().getTypeSpecifierKind() );
	}

	inline void setSpecifierKind(avm_type_specifier_kind_t aSpecifierKind)
	{
		refType().setSpecifierKind( aSpecifierKind );
	}


	/**
	 * GETTER - SETTER
	 * theSize
	 */
	inline std::size_t size() const
	{
		return( refType().size() );
	}

	inline void setSize(std::size_t aSize)
	{
		refType().setSize( aSize );
	}


	/**
	 * GETTER - SETTER
	 * theDataSize
	 */
	inline std::size_t getDataSize() const
	{
		return( refType().getDataSize() );
	}

	inline void setDataSize(std::size_t aDataSize)
	{
		refType().setDataSize( aDataSize );
	}

	/**
	 * GETTER - SETTER
	 * theBitSize
	 */
	inline std::size_t getBitSize() const
	{
		return( refType().getBitSize() );
	}

	inline void setBitSize(std::size_t aBitSize)
	{
		refType().setBitSize( aBitSize );
	}


	/**
	 * SETTER
	 * theDataSize
	 */
	inline void updateSize()
	{
		refType().updateSize();
	}


	/**
	 * CONSTRAINT generation
	 * for a given parameter
	 */
	inline bool couldGenerateConstraint() const
	{
		return( refType().couldGenerateConstraint() );
	}

	inline BF genConstraint(const BF & aParam) const
	{
		return( refType().genConstraint( aParam ) );
	}


	/**
	 * GETTER - SETTER
	 * theDefaultValue
	 */
	inline const BF & getDefaultValue() const
	{
		return( refType().getDefaultValue() );
	}

	inline bool hasDefaultValue() const
	{
		return( refType().hasDefaultValue() );
	}

	inline void setDefaultValue(const BF & aDefaultValue)
	{
		refType().setDefaultValue( aDefaultValue );
	}


	/**
	 * GETTER - SETTER
	 * theConstraint
	 */
	inline const BF & getConstraint() const
	{
		return( refType().getConstraint() );
	}

	inline bool hasConstraint() const
	{
		return( refType().hasConstraint() );
	}

	inline void saveConstraint(Element * aConstraint)
	{
		refType().saveConstraint( aConstraint );
	}

	inline void setConstraint(const BF & aConstraint)
	{
		refType().setConstraint( aConstraint );
	}


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// TypeAliasSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	TypeAliasSpecifier & alias();

	const TypeAliasSpecifier & alias() const;

	TypeAliasSpecifier * rawAlias() const;

	const BaseTypeSpecifier & aliasTypeSpecifier() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// BaseSymbolTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	BaseSymbolTypeSpecifier * rawSymbol() const;

	/**
	 * GETTER - SETTER
	 * the TableOfSymbol
	 */
	void saveSymbol(InstanceOfData * anInstance);

	const Symbol & getSymbol(
			const std::string & aFullyQualifiedNameID) const;

	const Symbol & getSymbolByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const Symbol & getSymbolByNameID(const std::string & aNameID) const;

	const Symbol & getSymbolByAstElement(
			const ObjectElement & astElement) const;

	bool hasSymbol() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// ClassTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	ClassTypeSpecifier & classT();

	const ClassTypeSpecifier & classT() const;

	ClassTypeSpecifier * rawClass() const;

//	operator ClassTypeSpecifier * () const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// EnumTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	EnumTypeSpecifier & enumT();

	const EnumTypeSpecifier & enumT() const;

	EnumTypeSpecifier * rawEnum() const;

//	operator EnumTypeSpecifier * () const;


	bool hasSymbolDataWithValue(const BF & aValue) const;

	const Symbol & getSymbolDataByValue(const BF & aValue) const;


	std::size_t getRandomSymbolOffset();

	const Symbol & getRandomSymbolData();

	const BF & getRandomSymbolValue();

	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// ContainerTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	ContainerTypeSpecifier & container();

	const ContainerTypeSpecifier & container() const;

	ContainerTypeSpecifier * rawContainer() const;

//	operator ContainerTypeSpecifier * () const;

	/**
	 * theContentsTypeSpecifier
	 */
	const TypeSpecifier & getContentsTypeSpecifier() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// IntervalTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	IntervalTypeSpecifier & interval();

	const IntervalTypeSpecifier & interval() const;

	IntervalTypeSpecifier * rawInterval() const;

//	operator IntervalTypeSpecifier * () const;

	/**
	 * theIntervalTypeSpecifier
	 */
	const TypeSpecifier & getSupportTypeSpecifier() const;


	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	// UnionTypeSpecifier
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////

	UnionTypeSpecifier & unionT();

	const UnionTypeSpecifier & unionT() const;

	UnionTypeSpecifier * rawUnion() const;

	operator UnionTypeSpecifier * () const;



	////////////////////////////////////////////////////////////////////////////
	// Serialization
	////////////////////////////////////////////////////////////////////////////

	/**
	 * Format a value w.r.t. its type
	 */
	inline void formatStream(OutStream & os, const BF & bfValue) const
	{
		if( mPTR != nullptr )
		{
			refType().formatStream( os , bfValue );
		}
		else
		{
			os << TAB << "Type::formatStream<null>" << EOL_FLUSH;
		}
	}

	inline void formatStream(OutStream & os, const ArrayBF & arrayValue) const
	{
		if( mPTR != nullptr )
		{
			refType().formatStream( os , arrayValue );
		}
		else
		{
			os << TAB << "Type::formatStream<null>" << EOL_FLUSH;
		}
	}


	inline std::string strT() const
	{
		return( ( mPTR != nullptr ) ? refType().strT() : "Type::strT<null>" );
	}

	inline void strHeader(OutStream & os) const override
	{
		if( mPTR != nullptr )
		{
			refType().strHeader(os);
		}
		else
		{
			os << "null< TypeSpecifier >";
		}
	}


	virtual void toStream(OutStream & os) const override
	{
		if( mPTR != nullptr )
		{
			refType().toStream( os );
		}
		else
		{
			os << TAB << "Type::stream<null>" << EOL_FLUSH;
		}
	}

	inline virtual void toFscn(OutStream & os) const
	{
		if( mPTR != nullptr )
		{
			refType().toFscn( os );
		}
		else
		{
			os << TAB << "Type::fscn<null>" << EOL_FLUSH;
		}
	}

	inline virtual std::string toString(
			const AvmIndent & indent = AVM_TAB_INDENT) const override
	{
		StringOutStream oss(indent);

		toStream( oss );

		return( oss.str() );
	}

	inline virtual std::string str() const override
	{
		return( ( mPTR != nullptr ) ? refType().str() : "Type::str<null>" );
	}

	inline virtual std::string strNum(
			uint8_t precision = AVM_MUMERIC_PRECISION) const override
	{
		return( ( mPTR != nullptr ) ?
				refType().strNum(precision) : "Type::num<null>" );
	}

};


/**
 * operator<<
 */
//AVM_OS_STREAM( TypeSpecifier )


} /* namespace sep */

#endif /* TYPESPECIFIER_H_ */
