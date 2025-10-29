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

#include "BuiltinContainer.h"

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/BuiltinQueue.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/type/ContainerTypeSpecifier.h>



namespace sep
{


/**
 * CREATION
 */
BuiltinContainer * BuiltinContainer::create(
		const ContainerTypeSpecifier & containerT)
{
	switch( containerT.getTypeSpecifierKind() )
	{
		case TYPE_VECTOR_SPECIFIER:
		{
			return( new BuiltinVector(containerT.size()) );
		}
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		{
			return( new BuiltinReverseVector(containerT.size()) );
		}

		case TYPE_LIST_SPECIFIER:
		{
			return( new BuiltinList(containerT.size()) );
		}

		case TYPE_SET_SPECIFIER:
		{
			return( new BuiltinSet(containerT.size()) );
		}

		case TYPE_MULTISET_SPECIFIER:
		{
			return( new BuiltinBag(containerT.size()) );
		}


		case TYPE_FIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		{
			return( new BuiltinFifo(containerT.size()) );
		}

		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			return( new BuiltinLifo(containerT.size()) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BuiltinContainer::create:> Unexpected "
						"CONTAINER type for instantiation > !!!"
					<< SEND_EXIT;

			return( new BuiltinList(containerT.size()) );
		}
	}
}


void BuiltinContainer::copy(const BuiltinArray & intputArray, std::size_t count)
{
	switch( intputArray.classKind() )
	{
		case FORM_ARRAY_BOOLEAN_KIND:
		{
			const ArrayBoolean & builtinArray = intputArray.to< ArrayBoolean >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_CHARACTER_KIND:
		{
			const ArrayCharacter & builtinArray = intputArray.to< ArrayCharacter >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newChar(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_INTEGER_KIND:
		{
			const ArrayInteger & builtinArray = intputArray.to< ArrayInteger >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_RATIONAL_KIND:
		{
			const ArrayRational & builtinArray = intputArray.to< ArrayRational >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(
						builtinArray.get(idx).first(),
						builtinArray.get(idx).second()) );
			}
			break;
		}
		case FORM_ARRAY_FLOAT_KIND:
		{
			const ArrayFloat & builtinArray = intputArray.to< ArrayFloat >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_STRING_KIND:
		{
			const ArrayString & builtinArray = intputArray.to< ArrayString >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newString(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_IDENTIFIER_KIND:
		{
			const ArrayIdentifier & builtinArray = intputArray.to< ArrayIdentifier >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newIdentifier(builtinArray.get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			const ArrayQualifiedIdentifier & builtinArray =
					intputArray.to< ArrayQualifiedIdentifier >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::
						newQualifiedIdentifier(builtinArray.get(idx)) );
			}
			break;
		}

		case FORM_ARRAY_BF_KIND:
		{
			const ArrayBF & builtinArray = intputArray.to< ArrayBF >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				if( builtinArray.get(idx).is_strictly< BuiltinArray >() )
				{
					add( BF( const_cast< ArrayBF * >( builtinArray.get(idx).
							to< BuiltinArray >().getArrayBF()) ));
				}
				else
				{
					add( builtinArray.get(idx) );
				}
			}
			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BuiltinContainer::copy:> "
						"Unexpected input array for copy !!!"
						<< SEND_EXIT;

			break;
		}
	}
}


/**
 * USUAL EQUAL
 */
int BuiltinContainer::compare(const BuiltinContainer & other) const
{
	if( this == &other )
	{
		return( 0 );
	}
	else
	{
		int  cmpResult = 0;

		for( std::size_t offset = 0 ;
			(offset < size()) && (offset < other.size()) ; ++offset )
		{
			cmpResult = this->at(offset).compare( other.at(offset) );
			if( cmpResult != 0  )
			{
				return( cmpResult );
			}
		}

		return( (size() == other.size()) ? 0 :
				((size() < other.size()) ? -1 : 1) );
	}
}


bool BuiltinContainer::isEQ(const BuiltinContainer & other) const
{
	if( size() == other.size() )
	{
		for( std::size_t offset = 0 ; offset < other.size() ; ++offset )
		{
			if( not this->at(offset).isEQ( other.at(offset) ) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}

/**
 * SYNTAXIC EQUAL
 */
bool BuiltinContainer::isSEQ(const BuiltinContainer & other) const
{
	if( size() == other.size() )
	{
		for( std::size_t offset = 0 ; offset < other.size() ; ++offset )
		{
			if( not this->at(offset).strEQ( other.at(offset) ) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}



}
