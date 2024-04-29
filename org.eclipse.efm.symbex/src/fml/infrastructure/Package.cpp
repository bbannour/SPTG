/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 22 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Package.h"

#include <fml/infrastructure/CompositePart.h>
#include <fml/infrastructure/PropertyPart.h>


namespace sep
{

/**
 * Serialization
 */

void Package::strHeader(OutStream & os) const
{
	os << getModifier().toString() << "package " << getNameID();
}


void Package::toStream(OutStream & os) const
{
	os << TAB << getModifier().toString()
			<< "package " << getNameID() << EOL << std::flush;

	if( mPackages.nonempty() )
	{
		os << TAB << "import:" << EOL;
		os << TAB2 << "include {" << EOL;
		TableOfMachine::const_raw_iterator it = mPackages.begin();
		TableOfMachine::const_raw_iterator endIt = mPackages.end();
		for( ; it != endIt ; ++it )
		{
			os << TAB3 << (it)->as_ptr< Package >()->getLocation() << ";" << EOL;
		}

		os << TAB2 << "}" << EOL2_FLUSH;
	}

	if( hasProperty() )
	{
		getPropertyPart().toStream(os);
		os << EOL;
	}

	if( mCompositeSpecification != nullptr )
	{
		mCompositeSpecification->toStream( os );
	}

	os << std::flush;
}


}
