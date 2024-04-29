/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "System.h"

#include <collection/Typedef.h>

#include <fml/infrastructure/Package.h>

#include <fml/workflow/WObject.h>


namespace sep
{

/**
 * Serialization
 */
void System::strHeader(OutStream & out) const
{
	out << getSpecifier().strFeature(" ")
		<< getModifier().toString()
		<< getSpecifier().strDesign_not(
				Specifier::DESIGN_PROTOTYPE_STATIC_KIND)
		<< getSpecifier().keywordComponent();

	if( getSpecifier().isDefined(Specifier::DISABLE_COMPONENT_DESIGN_FIELD) )
	{
		out << "< " << getSpecifier().str(
				Specifier::DISABLE_FCOMPONENT_EATURE_DESIGN_FIELD ) << " >";
	}

	out << " " << getNameID();
}


void System::toStream(OutStream & out) const
{
//	out << TAB << "@FormalML< system , 1.0 >:" << EOL2_FLUSH;
	out << TAB << "@xlia< system , 1.0 >:" << EOL2_FLUSH;

	if( hasWObject() &&
		(  getWObject()->isWProperty()
		|| getWObject()->hasOwnedElement()) )
	{
		getWObject()->toStream(out);
	}

	Machine::toStream(out);
}


}
