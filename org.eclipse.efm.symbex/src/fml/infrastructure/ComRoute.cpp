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

#include "ComRoute.h"

#include <fml/infrastructure/Connector.h>
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
 * SETTER
 * mComPoints
 */
void ComRoute::setComPoint(ComPoint * aComPoint,
		Modifier::DIRECTION_KIND ioDirection)
{
	mComPoints.append( BF(aComPoint) );

	if( getModifier().isDirectionUndefined() )
	{
		getwModifier().setDirectionKind( aComPoint->hasPort()
				? aComPoint->getPort()->getModifier().getDirectionKind()
				: ioDirection );
	}
}


/**
 * Serialization
 */
void ComRoute::toStream(OutStream & out) const
{
	out << TAB << getModifier().strDirection();

	toStreamProtocolCast( out ) << " " ;

	if( mComPoints.singleton() )
	{
		out << mComPoints.first().to_ptr< ComPoint >()->str() << ";" << EOL;
	}
	else
	{
		out << "{" << EOL;
		if( mComPoints.nonempty() )
		{
			BFList::const_raw_iterator< ComPoint > it = mComPoints.begin();
			BFList::const_raw_iterator< ComPoint > endIt = mComPoints.end();
			for( ; it != endIt ; ++it )
			{
				out << TAB2 << (it)->str() << ";" << EOL;
			}
		}
		out << TAB << "}" << EOL_FLUSH;
	}
}


} /* namespace sep */
