/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 déc. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TraceManager.h"


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void TraceManager::toStream(OutStream & os) const
{
	os << TAB << "Traces list :>" << EOL;

	const_iterator endIt = end();
	for( const_iterator it = begin() ; it != endIt ; ++it )
	{
		(*it)->toStream(os);
	}
	os << std::flush;
}



} /* namespace sep */
