/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmAnalysis.h"

namespace sep
{


std::string  STATIC_ANALYSIS::to_string(
		STATIC_ANALYSIS::VARIABLE_DEPENDENCY_RING status)
{
	switch ( status )
	{
		case DEPENDENT            : return( "dependent" );

		case INDEPENDENT          : return( "independent" );


		case UNDEFINED_DEPENDENCY : return( "undefined<dependency>" );

		case UNKNOWN_DEPENDENCY   :
		default                   : return( "unknown<dependency>" );
	}
}



} /* namespace sep */
