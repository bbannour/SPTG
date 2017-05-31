/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 févr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "Connector.h"

#include <fml/lib/IComPoint.h>

#include <fml/infrastructure/InteractionPart.h>
#include <fml/infrastructure/Machine.h>


namespace sep
{


std::string Connector::ANONYM_ID = "_#connector";


/**
 * CONSTRUCTOR
 * Default
 */
Connector::Connector(const InteractionPart & anInteractionPart)
: ObjectElement( CLASS_KIND_T( Connector ), anInteractionPart.getContainer()),
ComProtocol( PROTOCOL_UNDEFINED_KIND ),
mComRoutes( )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void Connector::toStream(OutStream & out) const
{
	out << TAB << getModifier().toString()
		<< (isPort() ? "connector" : "route");

	toStreamProtocolCast( out , true ) << " " << getNameID() <<  " {" << EOL;

	if( mComRoutes.nonempty() )
	{
		ScopeIncrIndent asii(out);

		route_iterator endIt = mComRoutes.end();
		for( route_iterator it = mComRoutes.begin() ; it != endIt ; ++it )
		{
			(*it)->toStream(out);
		}
	}

	out << TAB << "}" << EOL << std::flush;
}


}
