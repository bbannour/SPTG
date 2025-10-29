/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 nov. 2012
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "EnvironmentFactory.h"

#include <computer/instruction/InstructionEnvironment.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// LOADER / DISPOSER  API
////////////////////////////////////////////////////////////////////////////////

void EnvironmentFactory::load()
{
	InstructionEnvironment::initCache();
}

void EnvironmentFactory::dispose()
{
	InstructionEnvironment::finalizeCache();
}


} /* namespace sep */
