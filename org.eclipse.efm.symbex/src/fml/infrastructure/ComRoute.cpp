/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 oct. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include <fml/infrastructure/Connector.h>
#include "ComRoute.h"

#include <fml/infrastructure/Port.h>



namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
ComRoute::ComRoute(Connector * aContainer, const Modifier & aModifier)
: ObjectElement( CLASS_KIND_T( ComRoute ) , aContainer , aModifier ),
ComProtocol( PROTOCOL_UNDEFINED_KIND ),
mComPoints( )
{
	//!! NOTHING
}


/**
 * Serialization
 */
void ComRoute::toStream(OutStream & out) const
{
	out << TAB << getModifier().strDirection();

	toStreamProtocolCast( out ) << " " ;

	if( mComPoints.size() == 1 )
	{
		out << mComPoints.front().str() << ";" << EOL;
	}
	else
	{
		out << "{" << EOL;
		for( const auto & itComPoint : mComPoints )
		{
			out << TAB2 << itComPoint.str() << ";" << EOL;
		}
		out << TAB << "}" << EOL_FLUSH;
	}
}


} /* namespace sep */
