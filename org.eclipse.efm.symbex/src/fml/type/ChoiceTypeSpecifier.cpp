/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 juin 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#include "ChoiceTypeSpecifier.h"


namespace sep
{


/**
 * Serialization
 */
void ChoiceTypeSpecifier::toStream(OutStream & out) const
{
	if( out.preferablyFQN() )
	{
		out << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(out);

		return;
	}

	out << TAB << "type " << getFullyQualifiedNameID() << " choice {" << EOL;

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

		<< TAB << "choice:" << EOL_INCR_INDENT;

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
