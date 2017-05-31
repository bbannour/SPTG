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

#include "ClassTypeSpecifier.h"

#include <fml/expression/BuiltinArray.h>


namespace sep
{


/**
 * Format a value w.r.t. its type
 */
void ClassTypeSpecifier::formatStream(
		OutStream & out, const ArrayBF & arrayValue) const
{
	out << out.VALUE_STRUCT_CSS.BEGIN;

	avm_size_t offset = 1;
	TableOfSymbol::const_iterator it = getSymbolData().begin();
	TableOfSymbol::const_iterator itEnd = getSymbolData().end();
	if( it != itEnd )
	{
		(*it).getTypeSpecifier()->formatStream(out, arrayValue[0]);

		for( ++it ; (offset < arrayValue.size()) && (it != itEnd) ;
				++it , ++offset )
		{
			out << out.VALUE_STRUCT_CSS.SEPARATOR;
			(*it).getTypeSpecifier()->formatStream(out, arrayValue[offset]);
		}
	}

	for( ; offset < arrayValue.size() ; ++offset )
	{
		out << out.VALUE_STRUCT_CSS.SEPARATOR << arrayValue[offset].str();
	}

	out << out.VALUE_STRUCT_CSS.END ;
}


/**
 * Serialization
 */
void ClassTypeSpecifier::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << "type " << getFullyQualifiedNameID()
		<< ((isTypedUnion())? " union" : " struct") << " {" << EOL;

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

		<< TAB << "attribute:" << EOL;
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
