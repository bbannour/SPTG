/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 11 janv. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "UnionTypeSpecifier.h"


namespace sep
{


/**
 * Serialization
 */
void UnionTypeSpecifier::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << "type " << getFullyQualifiedNameID() << " union";

	out << " {" << EOL;

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
		<< TAB2 << "bit_size = " << getBitSize() << ";" << EOL

		<< TAB << "union:" << EOL_INCR_INDENT;

	getSymbolData().toStream(out);

	if( hasConstraint() )
	{
		out << TAB2 << "@constraint {" << EOL_INCR2_INDENT;
		getConstraint().toStream(out);
		out << DECR2_INDENT_TAB2 << "}" << EOL;
	}

	out << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */
