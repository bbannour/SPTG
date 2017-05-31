/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 12 avr. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCtorPrimitive.h"

#include <computer/EvaluationEnvironment.h>

#include <fml/type/BaseTypeSpecifier.h>


namespace sep
{


bool AvmPrimitive_Ctor::seval(EvaluationEnvironment & ENV)
{
	switch( ENV.inCODE->first().to_ptr<
			BaseTypeSpecifier >()->getTypeSpecifierKind() )
	{
		case TYPE_OPERATOR_SPECIFIER:
		case TYPE_AVMCODE_SPECIFIER:
		case TYPE_PORT_SPECIFIER:
		case TYPE_BUFFER_SPECIFIER:
		case TYPE_CONNECTOR_SPECIFIER:
		case TYPE_MACHINE_SPECIFIER:
			return( false );

		case TYPE_MESSAGE_SPECIFIER:
			return( false );

		default:
			return( false );
	}

	return( false );
}


} /* namespace sep */
