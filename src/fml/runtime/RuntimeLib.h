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

#ifndef RUNTIMELIB_H_
#define RUNTIMELIB_H_

#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>


namespace sep
{


class RuntimeLib
{

public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	RuntimeLib()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~RuntimeLib()
	{
		//!! NOTHING
	}


	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();



	/**
	 * PRE DEFINED RUNTIME MACHINE
	 */

	static RuntimeID RID_NIL;

	static RuntimeID RID_ENVIRONMENT;

};


}

#endif /* RUNTIMELIB_H_ */
