/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 3 nov. 2010
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "ExecutionSynchronizationPoint.h"


#include <fml/executable/RoutingData.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 * Serialization
 */
void ExecutionSynchronizationPoint::toStream(OutStream & os) const
{
	os << TAB << "esploc {" << EOL;


	os << TAB2 << "wpn = ";
	switch ( mAwaitingPointNature )
	{
		case AWAITING_POINT_INPUT_NATURE:
		{
			os << "AWAITING_POINT_INPUT_NATURE";
			break;
		}
		case AWAITING_POINT_OUTPUT_NATURE:
		{
			os << "AWAITING_POINT_OUTPUT_NATURE";
			break;
		}

		case AWAITING_POINT_JOIN_NATURE:
		{
			os << "AWAITING_POINT_JOIN_NATURE";
			break;
		}

		case AWAITING_POINT_UNDEFINED_NATURE:
		{
			os << "AWAITING_POINT_UNDEFINED_NATURE";
			break;
		}
		default :
		{
			os << "AWAITING_POINT_UNKNOWN_NATURE";
			break;
		}
	}
	os << ";" << EOL;

	os << TAB2 << "rid = " << mRID.str() << ";" << EOL_INCR_INDENT;

	if( mRoutingData != NULL )
	{
		mRoutingData.toStream(os);
	}

	if( mMessage.valid() )
	{
		mMessage.toStream(os);
	}

	if( next != NULL )
	{
		next->toStream(os);
	}

	os << DECR_INDENT_TAB <<  "}" << EOL;
}


}
