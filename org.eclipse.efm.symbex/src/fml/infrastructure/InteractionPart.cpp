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

#include "InteractionPart.h"

#include <fml/infrastructure/Machine.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
InteractionPart::InteractionPart(
		Machine * aContainer, const std::string & aNameID)
: ObjectClassifier( CLASS_KIND_T( InteractionPart ) , aContainer, aNameID),
ComProtocol( PROTOCOL_UNDEFINED_KIND ),
mConnectors( )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void InteractionPart::toStream(OutStream & out) const
{
	out << TAB << "@" << getNameID();

	toStreamProtocolCast( out ) << ":" << EOL_FLUSH;

	if( mConnectors.nonempty() )
	{
		ScopeIncrIndent asdii(out);

		const_connector_iterator it = mConnectors.begin();
		const_connector_iterator endIt = mConnectors.end();
		for( ; it != endIt ; ++it )
		{
			(it)->toStream(out);
		}
	}
}



}
