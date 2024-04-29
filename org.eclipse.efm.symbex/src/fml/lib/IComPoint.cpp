/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 juin 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "IComPoint.h"

namespace sep
{

////////////////////////////////////////////////////////////////////////////////
// COMMUNICATION POINT : KIND & DIRECTION
////////////////////////////////////////////////////////////////////////////////

IComPoint::ENUM_IO_NATURE IComPoint::to_nature(const std::string & id)
{
	if( id == "message"  ) return IO_MESSAGE_NATURE;

	if( id == "port"     ) return IO_PORT_NATURE;

	if( id == "signal"   ) return IO_SIGNAL_NATURE;

	return IO_UNDEFINED_NATURE;
}


std::string IComPoint::SEPARATOR = " % ";

std::string IComPoint::str_nature(
		IComPoint::ENUM_IO_NATURE nature, IComPoint::ENUM_IO_NATURE mask)
{
	std::string strNature = "";
	std::string sep = "";

	nature = nature & mask;

	if( (nature & IO_CHANNEL_NATURE) != 0 )
	{
		strNature = "channel";
		sep = SEPARATOR;
	}
	if( (nature & IO_MESSAGE_NATURE) != 0 )
	{
		strNature = "message";
		sep = SEPARATOR;
	}
	if( (nature & IO_PORT_NATURE) != 0 )
	{
		strNature = "port";
		sep = SEPARATOR;
	}
	if( (nature & IO_SIGNAL_NATURE) != 0 )
	{
		strNature = "signal";
		sep = SEPARATOR;
	}

	return( strNature );
}

} /* namespace sep */
