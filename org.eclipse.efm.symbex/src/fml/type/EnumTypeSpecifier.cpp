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

#include "EnumTypeSpecifier.h"

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructorImpl.h>


namespace sep
{


/**
 * SETTER
 * mBound
 */
void EnumTypeSpecifier::updateBound()
{
	avm_integer_t min = 0;
	avm_integer_t max = 0;

	mIntegerEnumerationFlag = true;

	TableOfSymbol::const_iterator it = getSymbolData().begin();
	TableOfSymbol::const_iterator endIt = getSymbolData().end();
	for( ; it != endIt ; ++it )
	{
		if( (*it).getValue().isWeakInteger() )
		{
			if( (*it).getValue().toInteger() < min )
			{
				min = (*it).getValue().toInteger();
			}
			if( (*it).getValue().toInteger() > max )
			{
				max = (*it).getValue().toInteger();
			}
		}
		else if( mIntegerEnumerationFlag )
		{
			mIntegerEnumerationFlag = false;
			getwModifier().setFeatureUnsafe(true);
		}
	}

	mInfimum  = ExpressionConstructorNative::newInteger(min);
	mSupremum = ExpressionConstructorNative::newInteger(max);
}


void EnumTypeSpecifier::updateBound(avm_integer_t min, avm_integer_t max)
{
	mInfimum  = ExpressionConstructorNative::newInteger(min);
	mSupremum = ExpressionConstructorNative::newInteger(max);

	mIntegerEnumerationFlag = true;
}


/**
 * GETTER
 * newfresh Enum Value
 */
BF EnumTypeSpecifier::newfreshSymbolValue()
{
	if( getSymbolData().nonempty() )
	{
		BF newfreshVal = getSymbolData().last().getValue();

		if( newfreshVal.isWeakInteger() )
		{
			newfreshVal.incrExpr();
		}
		else
		{
			newfreshVal = ExpressionConstructorNative::
					newUInteger(getSymbolData().size() );
		}

		while( getSymbolDataByValue( newfreshVal ).valid() )
		{
			newfreshVal.incrExpr();
		}

		return( newfreshVal );
	}

	return( ExpressionConstructorNative::
			newUInteger( getSymbolData().size() ) );
}


/**
 * GETTER - SETTER
 * mSymbolData
 */
bool EnumTypeSpecifier::hasSymbolData(InstanceOfData * aSymbolData) const
{
	if( aSymbolData->getTypeSpecifier() == this )
	{
		return( true );
	}
	else
	{
		TableOfSymbol::const_iterator it = getSymbolData().begin();
		TableOfSymbol::const_iterator endIt = getSymbolData().end();
		for( ; it != endIt ; ++it )
		{
			if( (*it) == aSymbolData )
			{
				return( true );
			}
		}
	}

	return( false );
}

bool EnumTypeSpecifier::hasSymbolData(const BF & aSymbol) const
{
	if( aSymbol.is< InstanceOfData >() )
	{
		return( hasSymbolData( aSymbol.to_ptr< InstanceOfData >() ) );
	}

	TableOfSymbol::const_iterator it = getSymbolData().begin();
	TableOfSymbol::const_iterator endIt = getSymbolData().end();
	for( ; it != endIt ; ++it )
	{
		if( aSymbol.isEQ( *it ) )
		{
			return( true );
		}
	}

	return( false );
}


bool EnumTypeSpecifier::hasSymbolDataWithValue(const BF & aValue) const
{
	TableOfSymbol::const_iterator it = getSymbolData().begin();
	TableOfSymbol::const_iterator endIt = getSymbolData().end();
	for( ; it != endIt ; ++it )
	{
		if( aValue.isEQ( (*it).getValue() ) || aValue.isEQ( *it ) )
		{
			return( true );
		}
	}

	return( false );
}


const Symbol & EnumTypeSpecifier::getSymbolDataByValue(const BF & aValue) const
{
	TableOfSymbol::const_iterator it = getSymbolData().begin();
	TableOfSymbol::const_iterator endIt = getSymbolData().end();
	for( ; it != endIt ; ++it )
	{
		if( aValue.isEQ( (*it).getValue() ) || aValue.isEQ( (*it) ) )
		{
			return( (*it) );
		}
	}

	return( Symbol::REF_NULL );
}


avm_size_t EnumTypeSpecifier::getRandomSymbolOffset()
{
	return( RANDOM::gen_uint(0, getSymbolData().size() - 1) );
}

const Symbol & EnumTypeSpecifier::getRandomSymbolData()
{
	return( getSymbolData( getRandomSymbolOffset() ) );
}

const BF & EnumTypeSpecifier::getRandomSymbolValue()
{
	return( getRandomSymbolData().getValue() );
}


/**
 * CONSTRAINT generation
 * for a given parameter
 */

BF EnumTypeSpecifier::minConstraint(const BF & aParam) const
{
	return( ExpressionConstructorNative::gteExpr(aParam, getInfimum()) );
}

BF EnumTypeSpecifier::maxConstraint(const BF & aParam) const
{
	return( ExpressionConstructorNative::lteExpr(aParam, getSupremum()) );
}


BF EnumTypeSpecifier::genConstraint(const BF & aParam) const
{
	if( hasConstraint() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "TODO << EnumTypeSpecifier::genConstraint( "
				<< aParam << " ) >> with compiled constraint:" << std::endl
				<< getConstraint()
				<< SEND_EXIT;
	}

	if( mIntegerEnumerationFlag )
	{
		return( ExpressionConstructorNative::andExpr(
				ExpressionConstructorNative::gteExpr(aParam, getInfimum()),
				ExpressionConstructorNative::lteExpr(aParam, getSupremum())) );
	}
	else if( getSymbolData().nonempty() )
	{
		TableOfSymbol::const_iterator it = getSymbolData().begin();
		TableOfSymbol::const_iterator endIt = getSymbolData().end();
		BF allConstraint = ExpressionConstructorNative::eqExpr(
				aParam, (*it).getValue());
		for( ++it ; it != endIt ; ++it )
		{
			allConstraint.orExpr( ExpressionConstructorNative::eqExpr(
					aParam, (*it).getValue()) );
		}

		return( allConstraint );
	}
	else
	{
		return( ExpressionConstant::BOOLEAN_TRUE );
	}
}


/**
 * Serialization
 */
void EnumTypeSpecifier::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << "type " << getFullyQualifiedNameID() << " enum {" << EOL;

AVM_IF_DEBUG_FLAG( COMPILING )
	if( hasAstElement() )
	{
		out << TAB2 << "//compiled = "
			<< getAstFullyQualifiedNameID() << ";" << EOL;
	}
AVM_ENDIF_DEBUG_FLAG( COMPILING )

AVM_IF_DEBUG_FLAG( DATA )
	out << TAB << "property:" << EOL

		<< TAB2 << "size = " << size() << ";" << "   "/*EOL;
		<< TAB2*/ << "data_size = " << getDataSize() << ";" << "   "/*EOL;
		<< TAB2*/ << "bit_size = " << getBitSize() << ";" << EOL

		<< TAB << "symbol:" << EOL;
AVM_ENDIF_DEBUG_FLAG( DATA )

	if( hasConstraint() )
	{
		out << TAB2 << "@constraint {" << EOL_INCR2_INDENT;
		getConstraint().toStream(out);
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	out << incr_stream( getSymbolData() ) << TAB << "}" << EOL_FLUSH;
}


}
