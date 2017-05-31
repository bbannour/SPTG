/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SymbexControllerRequestManager.h"


namespace sep
{

void SymbexControllerRequestManager::osRequestor(
		OutStream & os, const std::string & label,
		const ListOfProcessorUnit & listofRequestor)
{
	os << TAB << label;

	if( listofRequestor.singleton() )
	{
		os << listofRequestor.first()->strUniqId();
	}
	else if( listofRequestor.populated() )
	{
		ListOfProcessorUnit::const_iterator itRequestor = listofRequestor.begin();
		ListOfProcessorUnit::const_iterator endRequestor = listofRequestor.end();

		os << (*itRequestor)->strUniqId();
		for( ++itRequestor ; itRequestor != endRequestor ; ++itRequestor )
		{
			os << " ;; " << (*itRequestor)->strUniqId();
		}
	}

	os << EOL_FLUSH;
}


} /* namespace sep */
