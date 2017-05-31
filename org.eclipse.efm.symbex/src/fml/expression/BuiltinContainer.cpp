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
BuiltinContainer * BuiltinContainer::create(ContainerTypeSpecifier * containerT)
{
	switch( containerT->getTypeSpecifierKind() )
	{
		case TYPE_VECTOR_SPECIFIER:
		{
			return( new BuiltinVector(containerT->size()) );
		}
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		{
			return( new BuiltinReverseVector(containerT->size()) );
		}

		case TYPE_LIST_SPECIFIER:
		{
			return( new BuiltinList(containerT->size()) );
		}

		case TYPE_SET_SPECIFIER:
		{
			return( new BuiltinSet(containerT->size()) );
		}

		case TYPE_MULTISET_SPECIFIER:
		{
			return( new BuiltinBag(containerT->size()) );
		}


		case TYPE_FIFO_SPECIFIER:
		case TYPE_MULTI_FIFO_SPECIFIER:
		{
			return( new BuiltinFifo(containerT->size()) );
		}

		case TYPE_LIFO_SPECIFIER:
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			return( new BuiltinLifo(containerT->size()) );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "BuiltinContainer::create:> Unexpected "
						"CONTAINER type for instantiation > !!!"
					<< SEND_EXIT;

			return( new BuiltinList(containerT->size()) );
		}
	}
}


void BuiltinContainer::copy(BuiltinArray * intputArray, avm_size_t count)
{
	switch( intputArray->classKind() )
	{
		case FORM_ARRAY_BOOLEAN_KIND:
		{
			ArrayBoolean * builtinArray = intputArray->to< ArrayBoolean >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_CHARACTER_KIND:
		{
			ArrayCharacter * builtinArray = intputArray->to< ArrayCharacter >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newChar(builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_INTEGER_KIND:
		{
			ArrayInteger * builtinArray = intputArray->to< ArrayInteger >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_RATIONAL_KIND:
		{
			ArrayRational * builtinArray = intputArray->to< ArrayRational >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(
						builtinArray->get(idx).first(),
						builtinArray->get(idx).second()) );
			}
			break;
		}
		case FORM_ARRAY_FLOAT_KIND:
		{
			ArrayFloat * builtinArray = intputArray->to< ArrayFloat >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newExpr(builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_STRING_KIND:
		{
			ArrayString * builtinArray = intputArray->to< ArrayString >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newString(
						builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_IDENTIFIER_KIND:
		{
			ArrayIdentifier * builtinArray = intputArray->to< ArrayIdentifier >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::newIdentifier(builtinArray->get(idx)) );
			}
			break;
		}
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			ArrayQualifiedIdentifier * builtinArray =
					intputArray->to< ArrayQualifiedIdentifier >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				add( ExpressionConstructor::
						newQualifiedIdentifier(builtinArray->get(idx)) );
			}
			break;
		}

		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * builtinArray = intputArray->to< ArrayBF >();
			for( avm_size_t idx = 0 ; idx < count ; ++idx )
			{
				if( builtinArray->get(idx).is_strictly< BuiltinArray >() )
				{
					add( BF(builtinArray->get(idx).
							to_ptr< BuiltinArray >()->getArrayBF()) );
				}
				else
				{
					add( builtinArray->get(idx) );
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


}
