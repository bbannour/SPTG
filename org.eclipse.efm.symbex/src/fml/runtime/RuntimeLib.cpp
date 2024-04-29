/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 13 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "RuntimeLib.h"


#include <fml/executable/ExecutableLib.h>

#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


/**
 * PRE DEFINED RUNTIME MACHINE
 */
RuntimeID RuntimeLib::RID_NIL;

RuntimeID RuntimeLib::RID_ENVIRONMENT;


/**
 * LOADER
 */
void RuntimeLib::load()
{
	RID_NIL.create(-1, 0, ExecutableLib::MACHINE_NULL.rawMachine());
	RID_NIL.setQualifiedNameID("null#machine" /*"$null<machine>"*/);

	ExecutableLib::MACHINE_NULL.setRuntimeRID( RID_NIL );

	RID_ENVIRONMENT.create(-2, 0,
			ExecutableLib::MACHINE_ENVIRONMENT.rawMachine());
	RID_ENVIRONMENT.setQualifiedNameID("$env");
}


/**
 * DISPOSER
 */
void RuntimeLib::dispose()
{
	RID_NIL.destroy();

	RID_ENVIRONMENT.destroy();
}



}
