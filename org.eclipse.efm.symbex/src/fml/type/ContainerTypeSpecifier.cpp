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

#include "ContainerTypeSpecifier.h"

#include <fml/expression/BuiltinArray.h>

#include <fml/type/TypeManager.h>


namespace sep
{


/**
 * CONSTRAINT generation
 * for a given parameter
 */
BF ContainerTypeSpecifier::genConstraint(const BF & aParam) const
{
	if( hasConstraint() )
	{
		AVM_OS_FATAL_ERROR_EXIT
				<< "TODO << ContainerTypeSpecifier::genConstraint( "
				<< aParam << " ) >> with compiled constraint:" << std::endl
				<< getConstraint()
				<< SEND_EXIT;
	}

	switch( mSpecifierKind )
	{
		case TYPE_TIME_SPECIFIER:
		case TYPE_DISCRETE_TIME_SPECIFIER:
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		{
			if( mContentsTypeSpecifier.valid() )
			{
				return( mContentsTypeSpecifier.genConstraint(aParam) );
			}
			else
			{
				return( ExpressionConstant::BOOLEAN_TRUE );
			}
		}

		default:
		{
			return( ExpressionConstant::BOOLEAN_TRUE );
		}
	}
}


/**
 * Format a value w.r.t. its type
 */
void ContainerTypeSpecifier::formatStream(
		OutStream & os, const ArrayBF & arrayValue) const
{
	const SymbexValueCSS & VALUE_CSS = ( isTypedArray() ?
			os.VALUE_ARRAY_CSS : os.VALUE_STRUCT_CSS );

	os << VALUE_CSS.BEGIN;

	mContentsTypeSpecifier.formatStream(os, arrayValue[0]);
	for( avm_size_t offset = 1 ; offset < arrayValue.size() ; ++offset )
	{
		os << VALUE_CSS.SEPARATOR;
		mContentsTypeSpecifier.formatStream(os, arrayValue[offset]);
	}

	os << VALUE_CSS.END;
}


/**
 * Serialization
 */
std::string ContainerTypeSpecifier::strSpecifierKing(
		avm_type_specifier_kind_t aSpecifierKind)
{
	switch( aSpecifierKind )
	{
		case TYPE_ARRAY_SPECIFIER:
		{
			return( "array" );
		}

		case TYPE_LIST_SPECIFIER:
		{
			return( "list" );
		}
		case TYPE_VECTOR_SPECIFIER:
		{
			return( "vector" );
		}
		case TYPE_REVERSE_VECTOR_SPECIFIER:
		{
			return( "rvector" );
		}

		case TYPE_FIFO_SPECIFIER:
		{
			return( "fifo" );
		}
		case TYPE_LIFO_SPECIFIER:
		{
			return( "lifo" );
		}

		case TYPE_MULTI_FIFO_SPECIFIER:
		{
			return( "multififo" );
		}
		case TYPE_MULTI_LIFO_SPECIFIER:
		{
			return( "multilifo" );
		}

		case TYPE_SET_SPECIFIER:
		{
			return( "set" );
		}

		case TYPE_MULTISET_SPECIFIER:
		{
			return( "multiset" );
		}

		case TYPE_CLOCK_SPECIFIER:
		{
			return( "clock" );
		}
		case TYPE_TIME_SPECIFIER:
		{
			return( "time" );
		}
		case TYPE_CONTINUOUS_TIME_SPECIFIER:
		{
			return( "ctime" );
		}
		case TYPE_DISCRETE_TIME_SPECIFIER:
		{
			return( "dtime" );
		}

		default:
		{
			return( "container<?>" );
		}
	}
}

std::string ContainerTypeSpecifier::strType() const
{
	std::ostringstream os;

	if( isTypedArray() )
	{
		os << mContentsTypeSpecifier.strT() << "[ " << mMaximumSize << " ]";
	}
	else if( isTypedClockTime() && (mMaximumSize == 1) )
	{
		os  << ContainerTypeSpecifier::strSpecifierKing(mSpecifierKind)
//			<< " " << mContentsTypeSpecifier.strT();
			<< "< " << mContentsTypeSpecifier.strT() << " >";
	}
	else
	{
		os  << ContainerTypeSpecifier::strSpecifierKing(mSpecifierKind)
			<< "< " << mContentsTypeSpecifier.strT();
		if( mMaximumSize >= 0 )
		{
			os << " , " << mMaximumSize;
		}
		os << " >";
	}
	/**
	 * Serialization
	 */

	return( os.str() );
}


void ContainerTypeSpecifier::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(os);

		return;
	}

	os << TAB << "type " << getFullyQualifiedNameID() << " " << strType();

	os << " {" << EOL;

	os << TAB << "property:" << EOL;

	//os << TAB2 << "size = " << size() << ";" << EOL;

	os << TAB2 << "data_size = " << getDataSize() << ";" << "   "/*EOL;

	os << TAB2*/ << "bit_size = " << getBitSize() << ";" << EOL;

	if( hasConstraint() )
	{
		os << TAB2 << "@constraint {" << EOL_INCR2_INDENT;
		getConstraint().toStream(os);
		os << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	os << TAB << "}" << EOL_FLUSH;
}


}
