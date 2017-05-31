/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 7 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseTypeSpecifier.h"

#include <fml/expression/BuiltinArray.h>
#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>

#include <fml/type/TypeAliasSpecifier.h>


namespace sep
{


std::string BaseTypeSpecifier::TYPE_ANOMYM_ID = "type#anonym";

/**
 * SETTER
 * updateFullyQualifiedNameID()
 */
void BaseTypeSpecifier::updateFullyQualifiedNameID()
{
	if( hasFullyQualifiedNameID() )
	{
		if( hasAstElement() )
		{
			setNameID( getAstNameID() );
		}
		else
		{
			setNameID( NamedElement::extractNameID(
					getFullyQualifiedNameID() ) );
		}
	}
	else if( hasAstElement() )
	{
		std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();

		setAllNameID( "type" + aFullyQualifiedNameID.substr(
					aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR)),
				getAstNameID() );
	}
	else
	{
		setAllNameID( TYPE_ANOMYM_ID , TYPE_ANOMYM_ID );
	}
}


/**
 * CONSTRAINT generation
 * for a given parameter
 */

bool BaseTypeSpecifier::couldGenerateConstraint() const
{
	switch( mSpecifierKind )
	{
		case TYPE_ENUM_SPECIFIER:
		case TYPE_INTERVAL_SPECIFIER:
		{
			return( true );
		}

		case TYPE_INTEGER_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:
		case TYPE_REAL_SPECIFIER:
		{
			return( hasBitSizeConstraint() );
		}

		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
//		case TYPE_CONTINUOUS_TIME_SPECIFIER:
//		case TYPE_DISCRETE_TIME_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		{
			return( true );
		}

		default:
		{
			return( false );
		}
	}
}




inline static avm_integer_t pow2(avm_size_t n)
{
	return( 1 << n );

//	avm_integer_t res = 1;
//	for( ; 0 < n; --n )
//	{
//		res *= 2;
//	}
//	return( res );
}



avm_integer_t BaseTypeSpecifier::minIntegerValue() const
{
	const avm_size_t dim = getBitSize();

	switch( mSpecifierKind )
	{
		case TYPE_INTEGER_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( - pow2(dim - 1) );
			}
			else
			{
				return( AVM_NUMERIC_MIN_INTEGER );
			}
		}

		case TYPE_POS_INTEGER_SPECIFIER:
		{
			return( 1 );
		}

		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( 0 );
		}

		default:
		{
			return( AVM_NUMERIC_MIN_INTEGER );
		}
	}
}


avm_uinteger_t BaseTypeSpecifier::maxIntegerValue() const
{
	const avm_size_t dim = getBitSize();

	switch( mSpecifierKind )
	{
		case TYPE_INTEGER_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( pow2(dim - 1) - 1 );
			}
			else
			{
				return( AVM_NUMERIC_MAX_INTEGER );
			}
		}

		case TYPE_POS_INTEGER_SPECIFIER:
		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( pow2(dim) );
			}
			else
			{
				return( AVM_NUMERIC_MAX_UINTEGER );
			}
		}

		default:
		{
			return( AVM_NUMERIC_MAX_UINTEGER );
		}
	}
}


BF BaseTypeSpecifier::genConstraint(const BF & aParam) const
{
	if( hasConstraint() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "TODO << TypeSpecifier::genConstraint( "
				<< aParam << " ) >> with compiled constraint:" << std::endl
				<< getConstraint()
				<< SEND_EXIT;
	}

	const avm_size_t dim = getBitSize();

	switch( mSpecifierKind )
	{
		case TYPE_INTEGER_SPECIFIER:
		case TYPE_RATIONAL_SPECIFIER:
		case TYPE_FLOAT_SPECIFIER:
		case TYPE_REAL_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( ExpressionConstructorNative::andExpr(
						ExpressionConstructorNative::gteExpr(aParam,
								ExpressionConstructorNative::newInteger(
										(- pow2(dim - 1)))),
						ExpressionConstructorNative::lteExpr(aParam,
								ExpressionConstructorNative::newInteger(
										pow2(dim - 1) - 1))) );
			}
			else
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
		}

		case TYPE_UINTEGER_SPECIFIER:
		case TYPE_URATIONAL_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
		case TYPE_UFLOAT_SPECIFIER:
		case TYPE_UREAL_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( ExpressionConstructorNative::andExpr(
						ExpressionConstructorNative::gteExpr(aParam,
								ExpressionConstant::INTEGER_ZERO),
						ExpressionConstructorNative::lteExpr(aParam,
								ExpressionConstructorNative::newInteger(
										pow2(dim)))) );
			}
			else
			{
				return( ExpressionConstructorNative::gteExpr(aParam,
						ExpressionConstant::INTEGER_ZERO) );
			}
		}

		case TYPE_POS_INTEGER_SPECIFIER:
		{
//			if( hasBitSizeConstraint() )
			if( (dim > 0) && (dim <= 64) )
			{
				return( ExpressionConstructorNative::andExpr(
						ExpressionConstructorNative::gtExpr(aParam,
								ExpressionConstant::INTEGER_ZERO),
						ExpressionConstructorNative::lteExpr(aParam,
								ExpressionConstructorNative::newInteger(
										pow2(dim)))) );
			}
			else
			{
				return( ExpressionConstructorNative::gtExpr(aParam,
						ExpressionConstant::INTEGER_ZERO) );
			}
		}

		default:
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
	}
}


/**
 * GETTER
 * refered (as typedef) TypeSpecifier
 */
BaseTypeSpecifier * BaseTypeSpecifier::referedTypeSpecifier()
{
	return( this->isTypedAlias() ?
			as< TypeAliasSpecifier >()->targetTypeSpecifier() : this );
}


/**
 * Format a value w.r.t. its type
 */
void BaseTypeSpecifier::formatStream(
		OutStream & out, const BF & bfValue) const
{
	if( bfValue.is< ArrayBF >() )
	{
		formatStream(out, bfValue.as_ref< ArrayBF >());
	}
	else
	{
		out << bfValue.str();
	}
}

void BaseTypeSpecifier::formatStream(
		OutStream & out, const ArrayBF & arrayValue) const
{
	formatStream(out, arrayValue[0]);
	for( avm_size_t offset = 1 ; offset < arrayValue.size() ; ++offset )
	{
		out << out.VALUE_STRUCT_CSS.SEPARATOR;
		formatStream(out, arrayValue[offset]);
	}
}


/**
 * Serialization
 */
void BaseTypeSpecifier::strHeader(OutStream & out) const
{
	out << "type< " << strSpecifierKind() << " > " << getFullyQualifiedNameID();
}

void BaseTypeSpecifier::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << "type<base> " << getFullyQualifiedNameID()
		<< " as " << strSpecifierKind() << " {" << EOL;

AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

	out << TAB << "property:" << EOL

		<< TAB2 << "size = " << size() << ";" << EOL
		<< TAB2 << "data_size = " << getDataSize() << ";" << EOL
		<< TAB2 << "bit_size = " << getBitSize() << ";" << EOL;

	if( hasDefaultValue() )
	{
		out << TAB2 << "default = " << getDefaultValue().str() << ";" << EOL;
	}

	if( hasConstraint() )
	{
		out << TAB2 << "constraint {" << INCR2_INDENT;
		getConstraint().toStream(out);
		out << DECR2_INDENT_TAB << "}" << EOL;
	}

	out << TAB << "}" << EOL_FLUSH;
}


}
