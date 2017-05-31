/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 avr. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmLang.h"

#include <fml/expression/ExpressionConstructor.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// GENERIC XLIA SYNTAX
////////////////////////////////////////////////////////////////////////////////

BF XLIA_SYNTAX::ID_ALL = ExpressionConstructor::newIdentifier( "[*]" );


////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

void XLIA_SYNTAX::load()
{
	//!! NOTHING
}


void XLIA_SYNTAX::dispose()
{
	ID_ALL.destroy();
}


////////////////////////////////////////////////////////////////////////////////
// VARIABLE DATA
////////////////////////////////////////////////////////////////////////////////

/**
 * COMMUNICATION PROTOCOL KIND TO STRING
 */

#define PRINT_POINTER_NATURE( OBJ )   \
	case IPointerDataNature::POINTER_##OBJ##_NATURE :  \
			return( QUOTEME( POINTER_##OBJ ) )

std::string IPointerDataNature::strPointerDataNature(
		IPointerDataNature::POINTER_DATA_NATURE aNature)
{
	switch ( aNature )
	{
		PRINT_POINTER_NATURE( STANDARD );

		PRINT_POINTER_NATURE( FIELD_ARRAY_INDEX );
		PRINT_POINTER_NATURE( FIELD_ARRAY_OFFSET );
		PRINT_POINTER_NATURE( FIELD_CLASS_ATTRIBUTE );
		PRINT_POINTER_NATURE( FIELD_UNION_ATTRIBUTE );

		PRINT_POINTER_NATURE( ENUM_SYMBOL );

		PRINT_POINTER_NATURE( UFI_OFFSET );
		PRINT_POINTER_NATURE( UFI_MIXED );

		PRINT_POINTER_NATURE( UFI_RUNTIME );

		PRINT_POINTER_NATURE( UNDEFINED );

		default :  return( "POINTER_UNKNOWN_NATURE" );
	}
}

std::string IPointerDataNature::strPointer(const POINTER_DATA_NATURE aNature)
{
	switch ( aNature )
	{
		case IPointerDataNature::POINTER_STANDARD_NATURE:
		{
			return( "std" );
		}

		case IPointerDataNature::POINTER_FIELD_ARRAY_INDEX_NATURE:
		{
			return( "index#symbex" );
		}
		case IPointerDataNature::POINTER_FIELD_ARRAY_OFFSET_NATURE:
		{
			return( "index#offset" );
		}
		case IPointerDataNature::POINTER_FIELD_CLASS_ATTRIBUTE_NATURE:
		{
			return( "attr" );
		}
		case IPointerDataNature::POINTER_FIELD_CHOICE_ATTRIBUTE_NATURE:
		{
			return( "choice" );
		}
		case IPointerDataNature::POINTER_FIELD_UNION_ATTRIBUTE_NATURE:
		{
			return( "union" );
		}
		case IPointerDataNature::POINTER_ENUM_SYMBOL_NATURE:
		{
			return( "enum" );
		}

		case IPointerDataNature::POINTER_UFI_OFFSET_NATURE:
		{
			return( "ufi" );
		}
		case IPointerDataNature::POINTER_UFI_MIXED_NATURE:
		{
			return( "mix" );
		}

		case IPointerDataNature::POINTER_UFI_RUNTIME_NATURE:
		{
			return( "runtime" );
		}

		case IPointerDataNature::POINTER_UNDEFINED_NATURE:
		{
			return( "undef" );
		}

		default :
		{
			return( strPointerDataNature(aNature) );
		}
	}
}


} /* namespace sep */
