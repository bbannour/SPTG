/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 15 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TypeAliasSpecifier.h"


namespace sep
{

/**
 * Serialization
 */
void TypeAliasSpecifier::toStream(OutStream & os) const
{
	if( os.preferablyFQN() )
	{
		os << TAB << getFullyQualifiedNameID();

		AVM_DEBUG_REF_COUNTER(os);

		return;
	}

	os << TAB << "type " << getNameID() << " " << mTargetSpecifierType.strT();

	if( hasConstraint() )
	{
		os << " {" << EOL_TAB2 << "@constraint {" << EOL_INCR2_INDENT;
		getConstraint().toStream(os);
		os << DECR2_INDENT_TAB2 << "}" << EOL_TAB << "}";
	}
	else
	{
		os << ";";
	}

	os << EOL_FLUSH;
}


} /* namespace sep */
