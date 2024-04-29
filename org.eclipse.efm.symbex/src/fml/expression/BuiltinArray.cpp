/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 févr. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BuiltinArray.h"

#include <fml/executable/AvmInstruction.h>

#include <fml/builtin/Boolean.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/builtin/Identifier.h>
#include <fml/builtin/String.h>
#include <fml/builtin/QualifiedIdentifier.h>

#include <fml/type/BaseSymbolTypeSpecifier.h>
#include <fml/type/TypeManager.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Copy
 */
ArrayBF::ArrayBF(const ArrayBF & anArray)
: _BuiltinArray_< BF >( anArray ),
mElementTypeId( anArray.mElementTypeId ),
mInstruction( (anArray.mInstruction == nullptr) ? nullptr
		: new AvmInstruction( *(anArray.mInstruction) ) )
{
	//!!! NOTHING
}


/**
 * INTERFACE
 */
bool ArrayBF::contains(const BF & arg) const
{
	for( std::size_t offset = 0 ; offset < mSize ; ++offset )
	{
		if( mTable[offset] == arg )
		{
			return( true );
		}
	}

	return( false );
}


bool ArrayBF::startsWith(const ArrayBF & other) const
{
	if( mSize > other.mSize )
	{
		for( std::size_t offset = 0 ; offset < other.mSize ; ++offset )
		{
			if( mTable[offset] != other.mTable[offset] )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}


bool ArrayBF::endsWith(const ArrayBF & other) const
{
	if( mSize > other.mSize )
	{
		std::size_t pos = mSize - other.mSize;
		for( std::size_t offset = 0 ; pos < mSize ; ++pos , ++offset )
		{
			if( mTable[pos] != other.mTable[offset] )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}


/**
 * TRIVIALLY EQUAL
 */
bool ArrayBF::isTEQ(const ArrayBF & other) const
{
	if( this == &other )
	{
		return( true );
	}
	else if( mSize == other.mSize )
	{
		for( std::size_t offset = 0 ; offset < other.mSize ; ++offset )
		{
			if( not mTable[offset].isTEQ( other.mTable[offset] ) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}

/**
 * USUAL EQUAL
 */
int ArrayBF::compare(const ArrayBF & other) const
{
	if( this == &other )
	{
		return( 0 );
	}
	else
	{
		int  cmpResult = 0;

		for( std::size_t offset = 0 ;
			(offset < mSize) && (offset < other.mSize) ; ++offset )
		{
			cmpResult = mTable[offset].compare( other.mTable[offset] );
			if( cmpResult != 0  )
			{
				return( cmpResult );
			}
		}

		return( (mSize == other.mSize) ? 0 :
				((mSize < other.mSize) ? -1 : 1) );
	}
}

bool ArrayBF::isEQ(const ArrayBF & other) const
{
	if( mSize == other.mSize )
	{
		for( std::size_t offset = 0 ; offset < other.mSize ; ++offset )
		{
			if( not mTable[offset].isEQ( other.mTable[offset] ) )
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
bool ArrayBF::isSEQ(const ArrayBF & other) const
{
	if( mSize == other.mSize )
	{
		for( std::size_t offset = 0 ; offset < other.mSize ; ++offset )
		{
			if( not mTable[offset].strEQ( other.mTable[offset] ) )
			{
				return( false );
			}
		}

		return( true );
	}

	return( false );
}


/**
 * CONSTRUCTOR
 * Other
 */
ArrayBF::ArrayBF(const BFVector & anArray)
: _BuiltinArray_< BF >( CLASS_KIND_T( ArrayBF ),
		TypeManager::ARRAY_ANY, anArray),
mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
mInstruction( nullptr )
{
	//!!! NOTHING
}

ArrayBF::ArrayBF(
		const BaseTypeSpecifier & aTypeSpecifier, const BF & defaultValue)
: _BuiltinArray_< BF >( CLASS_KIND_T( ArrayBF ),
		aTypeSpecifier, aTypeSpecifier.size()),
mElementTypeId( ClassKindInfoInitializer::TYPE_UNDEFINED_ID ),
mInstruction( nullptr )
{
	setAll( defaultValue );
}



ArrayInteger::ArrayInteger(std::size_t aSize)
: _BuiltinArray_< avm_integer_t >( CLASS_KIND_T( ArrayInteger ),
		TypeManager::ARRAY_INTEGER, aSize)
{
	//!!! NOTHING
}

ArrayRational::ArrayRational(std::size_t aSize)
: _BuiltinArray_< PairInteger >( CLASS_KIND_T( ArrayRational ),
		TypeManager::ARRAY_RATIONAL, aSize)
{
	//!!! NOTHING
}

ArrayFloat::ArrayFloat(std::size_t aSize)
: _BuiltinArray_< double >( CLASS_KIND_T( ArrayFloat ),
		TypeManager::ARRAY_FLOAT, aSize)
{
	//!!! NOTHING
}

ArrayBoolean::ArrayBoolean(std::size_t aSize)
: _BuiltinArray_< bool >( CLASS_KIND_T( ArrayBoolean ),
		TypeManager::ARRAY_BOOLEAN, aSize)
{
	//!!! NOTHING
}

ArrayCharacter::ArrayCharacter(std::size_t aSize)
: _BuiltinArray_< char >( CLASS_KIND_T( ArrayCharacter ),
		TypeManager::ARRAY_CHARACTER, aSize)
{
	//!!! NOTHING
}

ArrayString::ArrayString(std::size_t aSize)
: _BuiltinArray_< std::string >( CLASS_KIND_T( ArrayString ),
		TypeManager::ARRAY_STRING, aSize)
{
	//!!! NOTHING
}

ArrayIdentifier::ArrayIdentifier(std::size_t aSize)
: _BuiltinArray_< std::string >( CLASS_KIND_T( ArrayIdentifier ),
		TypeManager::ARRAY_IDENTIFIER, aSize)
{
	//!!! NOTHING
}

ArrayQualifiedIdentifier::ArrayQualifiedIdentifier(std::size_t aSize)
: _BuiltinArray_< std::string >( CLASS_KIND_T( ArrayQualifiedIdentifier ),
		TypeManager::ARRAY_QUALIFIED_IDENTIFIER, aSize)
{
	//!!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// TO ARRAY
////////////////////////////////////////////////////////////////////////////////

class_kind_t BuiltinArray::getArrayTypeId(class_kind_t aTypeId)
{
	switch( aTypeId )
	{
		case FORM_BUILTIN_BOOLEAN_KIND:
		{
			return( FORM_ARRAY_BOOLEAN_KIND );
		}
		case FORM_BUILTIN_CHARACTER_KIND:
		{
			return( FORM_ARRAY_CHARACTER_KIND );
		}
		case FORM_BUILTIN_INTEGER_KIND:
		{
			return( FORM_ARRAY_INTEGER_KIND );
		}
		case FORM_BUILTIN_RATIONAL_KIND:
		{
			return( FORM_ARRAY_RATIONAL_KIND );
		}
		case FORM_BUILTIN_FLOAT_KIND:
		{
			return( FORM_ARRAY_FLOAT_KIND );
		}
		case FORM_BUILTIN_STRING_KIND:
		{
			return( FORM_ARRAY_STRING_KIND );
		}
		case FORM_BUILTIN_IDENTIFIER_KIND:
		{
			return( FORM_ARRAY_IDENTIFIER_KIND );
		}
		case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
		{
			return( FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND );
		}

		default:
		{
			return( FORM_ARRAY_BF_KIND );
		}
	}
}

class_kind_t BuiltinArray::getArrayTypeId(
		class_kind_t classKindA, class_kind_t classKindB)
{
	if( classKindA == classKindB )
	{
		return( classKindA );
	}
	else if( (classKindA == FORM_ARRAY_BF_KIND)
			|| (classKindB == FORM_ARRAY_BF_KIND) )
	{
		return( FORM_ARRAY_BF_KIND );
	}
	else
	{
		switch( classKindA )
		{
			case FORM_BUILTIN_INTEGER_KIND:
			case FORM_BUILTIN_RATIONAL_KIND:
			{
				if( classKindB == FORM_BUILTIN_FLOAT_KIND )
				{
					return( FORM_BUILTIN_FLOAT_KIND );
				}
				else
				{
					return( FORM_ARRAY_BF_KIND );
				}
			}
			case FORM_BUILTIN_FLOAT_KIND:
			{
				if( classKindB == FORM_BUILTIN_INTEGER_KIND )
				{
					return( FORM_BUILTIN_FLOAT_KIND );
				}
				else
				{
					return( FORM_ARRAY_BF_KIND );
				}
			}

			case FORM_BUILTIN_IDENTIFIER_KIND:
			{
				if( classKindB == FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND )
				{
					return( FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND );
				}
				else
				{
					return( FORM_ARRAY_BF_KIND );
				}
			}
			case FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND:
			{
				if( classKindB == FORM_BUILTIN_IDENTIFIER_KIND )
				{
					return( FORM_BUILTIN_QUALIFIED_IDENTIFIER_KIND );
				}
				else
				{
					return( FORM_ARRAY_BF_KIND );
				}
			}

			default:
			{
				return( FORM_ARRAY_BF_KIND );
			}
		}
	}
}


BF BuiltinArray::create(const BFVector & array)
{
	if( array.nonempty() )
	{
		BFVector::const_iterator itEnd = array.end();
		BFVector::const_iterator it = array.begin();

		class_kind_t aTypeId = (*it).classKind();

		for( ++it ; it != itEnd ; ++it )
		{
			aTypeId = BuiltinArray::getArrayTypeId( aTypeId , (*it).classKind() );
			if( aTypeId == FORM_ARRAY_BF_KIND )
			{
				break;
			}
		}

		switch( aTypeId = BuiltinArray::getArrayTypeId( aTypeId ) )
		{
			case FORM_ARRAY_BOOLEAN_KIND:
			{
				ArrayBoolean * builtinArray = new ArrayBoolean( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toBoolean());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_CHARACTER_KIND:
			{
				ArrayCharacter * builtinArray = new ArrayCharacter( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toBoolean());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_INTEGER_KIND:
			{
				ArrayInteger * builtinArray = new ArrayInteger( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toInteger());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_RATIONAL_KIND:
			{
				ArrayRational * builtinArray = new ArrayRational( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx,
							(*it).toNumerator(), (*it).toDenominator());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_FLOAT_KIND:
			{
				ArrayFloat * builtinArray = new ArrayFloat( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toFloat());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_STRING_KIND:
			{
				ArrayString * builtinArray = new ArrayString( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toBuiltinString());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_IDENTIFIER_KIND:
			{
				ArrayIdentifier * builtinArray = new ArrayIdentifier( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toIdentifier());
				}

				return( BF(builtinArray) );
			}
			case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
			{
				ArrayQualifiedIdentifier * builtinArray =
						new ArrayQualifiedIdentifier( array.size() );
				std::size_t idx = 0;
				for( it = array.begin() ; it != itEnd ; ++it, ++idx )
				{
					builtinArray->set(idx, (*it).toUfi());
				}

				return( BF(builtinArray) );
			}

			default:
			{
				return( BF(new ArrayBF(TypeManager::ARRAY_ANY, array)) );
			}
		}
	}

	return( BF(new ArrayBF(TypeManager::ARRAY_ANY, array)) );
}




////////////////////////////////////////////////////////////////////////////////
// CAST
////////////////////////////////////////////////////////////////////////////////

ArrayBF * ArrayInteger::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Integer ),
			TypeManager::ARRAY_INTEGER, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, ExpressionConstructor::newInteger(get(idx)));
	}

	return( bfArray );
}



ArrayBF * ArrayRational::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Rational ),
			TypeManager::ARRAY_RATIONAL, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, ExpressionConstructor::newRational(
				get(idx).first(), get(idx).second()));
	}

	return( bfArray );
}

ArrayBF * ArrayFloat::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Float ),
			TypeManager::ARRAY_FLOAT, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, ExpressionConstructor::newFloat(get(idx)));
	}

	return( bfArray );
}


ArrayBF * ArrayCharacter::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Character ),
			TypeManager::ARRAY_CHARACTER, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, ExpressionConstructor::newChar(get(idx)));
	}

	return( bfArray );
}



ArrayBF * ArrayBoolean::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Boolean ),
			TypeManager::ARRAY_BOOLEAN, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, ExpressionConstructor::newBoolean(get(idx)));
	}

	return( bfArray );
}



ArrayBF * ArrayString::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( String ),
			TypeManager::ARRAY_STRING, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, BF(new String(get(idx))));
	}

	return( bfArray );
}



ArrayBF * ArrayIdentifier::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( Identifier ),
			TypeManager::ARRAY_IDENTIFIER, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, BF(new Identifier(get(idx))));
	}

	return( bfArray );
}


ArrayBF * ArrayQualifiedIdentifier::getArrayBF() const
{
	ArrayBF * bfArray = new ArrayBF( CLASS_KIND_T( QualifiedIdentifier ),
			TypeManager::ARRAY_QUALIFIED_IDENTIFIER, size() );

	for( std::size_t idx = 0 ; idx < size() ; ++idx )
	{
		bfArray->set(idx, BF(new QualifiedIdentifier(get(idx))));
	}

	return( bfArray );
}


////////////////////////////////////////////////////////////////////////////////
// COPY
////////////////////////////////////////////////////////////////////////////////

void ArrayBF::copy(BuiltinArray * intputArray, std::size_t count)
{
	switch( intputArray->classKind() )
	{
		case FORM_ARRAY_BOOLEAN_KIND:
		{
			ArrayBoolean * builtinArray = intputArray->to_ptr< ArrayBoolean >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newBoolean(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_CHARACTER_KIND:
		{
			ArrayCharacter * builtinArray = intputArray->to_ptr< ArrayCharacter >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newChar(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_INTEGER_KIND:
		{
			ArrayInteger * builtinArray = intputArray->to_ptr< ArrayInteger >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newInteger(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_RATIONAL_KIND:
		{
			ArrayRational * builtinArray = intputArray->to_ptr< ArrayRational >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newRational(
								builtinArray->get(idx).first(),
								builtinArray->get(idx).second()));
			}
			break;
		}
		case FORM_ARRAY_FLOAT_KIND:
		{
			ArrayFloat * builtinArray = intputArray->to_ptr< ArrayFloat >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newFloat(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_STRING_KIND:
		{
			ArrayString * builtinArray = intputArray->to_ptr< ArrayString >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newString(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_IDENTIFIER_KIND:
		{
			ArrayIdentifier * builtinArray = intputArray->to_ptr< ArrayIdentifier >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::newIdentifier(builtinArray->get(idx)));
			}
			break;
		}
		case FORM_ARRAY_QUALIFIED_IDENTIFIER_KIND:
		{
			ArrayQualifiedIdentifier * builtinArray =
					intputArray->to_ptr< ArrayQualifiedIdentifier >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				set(idx, ExpressionConstructor::
						newQualifiedIdentifier(builtinArray->get(idx)));
			}
			break;
		}

		case FORM_ARRAY_BF_KIND:
		{
			ArrayBF * builtinArray = intputArray->to_ptr< ArrayBF >();
			for( std::size_t idx = 0 ; idx < count ; ++idx )
			{
				if( builtinArray->get(idx).is_strictly< BuiltinArray >() )
				{
					set(idx, BF(builtinArray->get(idx).
							to< BuiltinArray >().getArrayBF()));
				}
				else
				{
					set(idx, builtinArray->get(idx));
				}
			}
			break;
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "ArrayManager::copy:> Unexpected input array for copy !!!"
					<< SEND_EXIT;

			break;
		}
	}
}



/**
 ***************************************************************************
 * SERIALIZATION
 ***************************************************************************
 */

std::string ArrayBF::str() const
{
	StringOutStream oss( AVM_STR_INDENT );

AVM_IF_DEBUG_FLAG_AND( BYTECODE , hasInstruction() )

	AVM_DEBUG_DISABLE_FLAG( BYTECODE )

	toStream( oss << IGNORE_FIRST_TAB );

	AVM_DEBUG_ENABLE_FLAG( BYTECODE )

AVM_ELSE

	toStream( oss << IGNORE_FIRST_TAB );

AVM_ENDIF_DEBUG_FLAG_AND( BYTECODE )

	return( oss.str() );
}

void ArrayBF::toStream(OutStream & os) const
{
	os << TAB << AVM_DEBUG_REF_COUNTER();

AVM_IF_DEBUG_FLAG_AND( BYTECODE , hasInstruction() )
	getInstruction()->toStream(os);
AVM_ENDIF_DEBUG_FLAG_AND( BYTECODE )

	if( mTypeSpecifier->hasTypeStructureOrChoiceOrUnion() )
	{
		const BaseSymbolTypeSpecifier & strucT =
				mTypeSpecifier->as< BaseSymbolTypeSpecifier >();

AVM_IF_DEBUG_FLAG( DATA )
	os << "<" << strucT.strT() << ">";
AVM_ENDIF_DEBUG_FLAG( DATA )

		os << "{ ";
		if( mSize > 0 )
		{
			os << strucT.getSymbolData(0).strValue( mTable[0] );
			for( std::size_t idx = 1 ; idx < mSize ; ++idx )
			{
				os << " , " << strucT.getSymbolData(idx).strValue( mTable[idx] );
			}
		}
		os << " }";
	}
	else
	{
AVM_IF_DEBUG_FLAG( DATA )
	os << "<" << mTypeSpecifier->strT() << ">";
AVM_ENDIF_DEBUG_FLAG( DATA )

		os << ( mTypeSpecifier->isTypedArray() ?  "[ "  :  "{ " );
		if( mSize > 0 )
		{
			os << mTable[0].str();
			for( std::size_t idx = 1 ; idx < mSize ; ++idx )
			{
				os << " , " << mTable[idx].str();
			}
		}
		os << ( mTypeSpecifier->isTypedArray() ? " ]" : " }" );
	}

	os << EOL;
}




}
