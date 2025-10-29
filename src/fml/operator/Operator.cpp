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
#include "Operator.h"

#include <common/BF.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
Operator::Operator(
		const std::string & aFullyQualifiedNameID,
		const std::string & aNameID,
		AVM_OPCODE anAvmOpCode, AVM_OPCODE anOptimizedOpCode,
		ALGEBRA_QUALIFIER anAlgebraQualifier, FIX_NOTATION aFixNotation,
		const std::string & aStandardSymbol,
		const std::string & aSyntaxMIXFIX,
		const std::string & aSymbolQEPCAD)
: NamedElement(CLASS_KIND_T( Operator ),
		aFullyQualifiedNameID, aNameID, aStandardSymbol),
mAvmOpCode( anAvmOpCode ),
mOptimizedOpCode( anOptimizedOpCode ),
mOffset( 0 ),

mAlgebraQualifier( anAlgebraQualifier ),
mFixNotation( aFixNotation ),

mStandardSymbol( aStandardSymbol ),
mSyntaxMIXFIX( aSyntaxMIXFIX ),
mSymbolQEPCAD( aSymbolQEPCAD )
{
	//!! NOTHING
}



/**
 * Serialization
 */
void Operator::toStream(OutStream & os,
		ENUM_PRINT_OPERATOR_FORMAT printFormat) const
{
	switch( printFormat )
	{
		case PRINT_OPERATOR_NAME_FORMAT:
		{
			os << getNameID();
			break;
		}
		case PRINT_OPERATOR_SYMBOL_FORMAT:
		{
			os << mStandardSymbol;
			break;
		}
		case PRINT_OPERATOR_MIXFIX_FORMAT:
		{
			os << mSyntaxMIXFIX;
			break;
		}
		case PRINT_OPERATOR_CAS_QEPCAD_FORMAT:
		{
			os << mSymbolQEPCAD;
			break;
		}
		case PRINT_OPERATOR_UNDEFINED_FORMAT:
		default:
		{
			os << getFullyQualifiedNameID();
			break;
		}
	}

	os << std::flush;
}



}
