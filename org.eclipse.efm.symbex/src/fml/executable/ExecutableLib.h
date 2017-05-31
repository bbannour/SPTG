/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 juil. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef EXECUTABLELIB_H_
#define EXECUTABLELIB_H_

#include <common/BF.h>

#include <fml/symbol/Symbol.h>


namespace sep
{


class ExecutableLib
{

public:

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ExecutableLib()
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~ExecutableLib()
	{
		//!! NOTHING
	}

	/**
	 * LOADER - DISPOSER
	 */
	static void load();
	static void dispose();


	/**
	 * PRE DEFINED MACHINE VARIABLE
	 */
	static Symbol MACHINE_NULL;
	static Symbol MACHINE_ENVIRONMENT;

	static Symbol MACHINE_SELF;
	static Symbol MACHINE_PARENT;
	static Symbol MACHINE_COMMUNICATOR;

	static Symbol MACHINE_COMPONENT_SELF;
	static Symbol MACHINE_COMPONENT_PARENT;
	static Symbol MACHINE_COMPONENT_COMMUNICATOR;

	static Symbol MACHINE_SYSTEM;

	/**
	 * PRE DEFINED NULL FORM
	 */
	static Symbol CHANNEL_NIL;
	static Symbol PORT_NIL;
	static Symbol BUFFER_NIL;



	/**
	 * BOTTOM
	 * TOP
	 */
	static Symbol BOTTOM;
	static Symbol TOP;

	static Symbol _NULL_;

	static Symbol _INFINITY_;


};


}

#endif /* EXECUTABLELIB_H_ */
