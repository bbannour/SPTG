/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef TABLEOF
#define TABLEOF

#include <common/AvmObject.h>

#include <collection/Vector.h>

#include <fml/type/TypeSpecifier.h>

#include <collection/List.h>


namespace sep
{

class ObjectElement;


class TableOfTypeSpecifier :
		public AvmObject,
		public Vector< TypeSpecifier >,
		AVM_INJECT_INSTANCE_COUNTER_CLASS( TableOfTypeSpecifier )
{

	AVM_DECLARE_CLONABLE_BASE_CLASS( TableOfTypeSpecifier )


public:
	/**
	 * TYPEDEF
	 */
	typedef  BaseTypeSpecifier       *  PointerBaseT;
	typedef  const BaseTypeSpecifier *  ConstPointerBaseT;

	typedef  Vector< TypeSpecifier >    ContainerOfType;



public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TableOfTypeSpecifier()
	: AvmObject( ),
	ContainerOfType( )
	{
		//!! NOTHING
	}

	TableOfTypeSpecifier(std::size_t aSize)
	: AvmObject( ),
	ContainerOfType( aSize )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TableOfTypeSpecifier(const TableOfTypeSpecifier & aTable)
	: AvmObject( aTable ),
	ContainerOfType( aTable )
	{
		//!! NOTHING
	}

	TableOfTypeSpecifier(const ContainerOfType & aTable)
	: AvmObject( ),
	ContainerOfType( aTable )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TableOfTypeSpecifier()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 */
	inline const TypeSpecifier & get(std::size_t offset) const
	{
		AVM_OS_ASSERT_FATAL_ARRAY_OFFSET_EXIT( offset, ContainerOfType::size() )
				<< "Unbound TypeSpecifier offset !!!"
				<< SEND_EXIT;

		return( ContainerOfType::at(offset) );
	}


	inline const TypeSpecifier & getByQualifiedNameID(
			std::string aQualifiedNameID, NamedElement::op_comparer_t op) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).refType().isEqualsID(aQualifiedNameID, op) )
			{
				return( *it );
			}
		}
		return( TypeSpecifier::nullref() );
	}


	inline const TypeSpecifier & getByFQNameID(
			const std::string & aFullyQualifiedNameID) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			// STRICT:> compare LOCATOR & LOCATION [true:- retry only LOCATION]
			if( (*it).fqnEquals( aFullyQualifiedNameID , true ) )
			{
				return( *it );
			}
		}
		return( TypeSpecifier::nullref() );
	}


	inline const TypeSpecifier & getByQualifiedNameID(
			const std::string & aQualifiedNameID) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).refType().fqnEndsWith(aQualifiedNameID) )
			{
				return( *it );
			}
		}
		return( TypeSpecifier::nullref() );
	}


	inline const TypeSpecifier & getByNameID(const std::string & aNameID) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).getNameID() == aNameID )
			{
				return( *it );
			}
		}
		return( TypeSpecifier::nullref() );
	}


	inline const TypeSpecifier & getByAstElement(
			const ObjectElement & astElement) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			if( (*it).isAstElement( astElement ) )
			{
				return( *it );
			}
		}
		return( TypeSpecifier::nullref() );
	}


	/**
	 * SAVE
	 * APPEND
	 */
	inline const TypeSpecifier & save(PointerBaseT aType)
	{
		ContainerOfType::push_back( TypeSpecifier(aType) );

		return( ContainerOfType::back() );
	}

	inline void append(const TypeSpecifier & aType) override
	{
		ContainerOfType::append( aType );
	}


	/**
	 * SETTER
	 */
	inline void set(avm_offset_t offset, const TypeSpecifier & aType)
	{
		ContainerOfType::set(offset, aType);
	}

	inline void set(avm_offset_t offset, PointerBaseT aType)
	{
		ContainerOfType::set(offset, TypeSpecifier(aType));
	}


	/**
	 * contains a particular element
	 */
	inline bool contains(ConstPointerBaseT aType) const
	{
//		if( (aType->getOffset() < size())
//			&& (aType == get(aType->getOffset())) )
//		{
//			return( true );
//		}
//		else
		{
			ContainerOfType::const_iterator it = BaseVector::begin();
			ContainerOfType::const_iterator endIt = BaseVector::end();
			for( ; it != endIt ; ++it )
			{
				if( (*it) == aType )
				{
					return( true );
				}
			}

			return( false );
		}
	}


	inline bool contains(const TypeSpecifier & aType) const override
	{
		return( ContainerOfType::contains( aType ) );
	}


	/**
	 * Serialization
	 */
	virtual void toStream(OutStream & os) const override
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			(*it).toStream(os);
		}
	}

	virtual void toFscn(OutStream & os) const
	{
		ContainerOfType::const_iterator it = ContainerOfType::begin();
		ContainerOfType::const_iterator endIt = ContainerOfType::end();
		for( ; it != endIt ; ++it )
		{
			os << TAB << AVM_NO_INDENT;
			(*it).toFscn(os);
			os << END_INDENT_EOL;
		}
	}



	/**
	 * GETTER
	 * For Symbol in TypeSpecifier
	 */
	const Symbol & getSymbolData(
			const std::string & aFullyQualifiedNameID) const;

	const Symbol & getSymbolDataByQualifiedNameID(
			const std::string & aQualifiedNameID) const;

	const Symbol & getSymbolDataByNameID(const std::string & aNameID) const;

	const Symbol & getSymbolDataByAstElement(
			const ObjectElement & astElement) const;

};


} /* namespace sep */

#endif /* TABLEOF */
