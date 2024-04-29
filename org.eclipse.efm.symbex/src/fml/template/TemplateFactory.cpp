/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 nov. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TemplateFactory.h"

#include <fml/template/TimedMachine.h>

#include <fml/infrastructure/Machine.h>


namespace sep
{


void TemplateFactory::genProperty(Machine * machine)
{
	if( machine->getSpecifier().hasFeatureTimed() )
	{
		TimedMachine::genProperty(* machine);
	}
}


void TemplateFactory::genBehavior(Machine * machine)
{
	if( machine->getSpecifier().hasFeatureTimed() )
	{
		TimedMachine::genBehavior(* machine);
	}
}


} /* namespace sep */
