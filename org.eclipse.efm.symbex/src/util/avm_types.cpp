/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "avm_types.h"

namespace sep
{


std::string strUnit(avm_unit_t unit)
{
	switch ( unit )
	{
		case AVM_NANO_SECOND_UNIT  : return( "ns");
		case AVM_MICRO_SECOND_UNIT : return( "µs");
		case AVM_MILLI_SECOND_UNIT : return( "ms");
		case AVM_SECOND_UNIT       : return( "s");

		case AVM_MINUTE_UNIT       : return( "min");
		case AVM_HOUR_UNIT         : return( "h");

		case AVM_MICRO_STEP_UNIT   : return( "micro_step");
		case AVM_STEP_UNIT         : return( "step");
		case AVM_MACRO_STEP_UNIT   : return( "macro_step");

		case AVM_UNDEFINED_UNIT    : return( "undefined<unit>");

		default                    : return( "unknown<unit>" );
	}
}


}

