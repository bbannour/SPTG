/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 5 août 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "BaseInstanceForm.h"

#include <fml/executable/BaseAvmProgram.h>
#include <fml/executable/ExecutableForm.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/runtime/RuntimeID.h>


namespace sep
{

/**
 * GETTER
 * mContainer
 */
BaseAvmProgram * BaseInstanceForm::getContainer() const
{
	return( static_cast< BaseAvmProgram * >( mContainer ) );
}


/**
 * SETTER
 * mFullyQualifiedNameID
 */
void BaseInstanceForm::updateFullyQualifiedNameID()
{
	if( hasAstElement() )
	{
		std::string aFullyQualifiedNameID = getAstFullyQualifiedNameID();

		std::string::size_type pos =
				aFullyQualifiedNameID.find(FQN_ID_ROOT_SEPARATOR);
		if( pos != std::string::npos )
		{
			setFullyQualifiedNameID(
					"inst" + aFullyQualifiedNameID.substr(pos) );
		}
		else
		{
			setFullyQualifiedNameID( aFullyQualifiedNameID );
		}
	}
	else
	{
		setFullyQualifiedNameID("");
	}

	updateNameID();
}


}
