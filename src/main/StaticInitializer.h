/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 29 mai 2019
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef STATIC_INITIALIZER_H_
#define STATIC_INITIALIZER_H_


namespace sep
{


class StaticInitializer
{

protected:
	/**
	 * STATIC ATTRIBUTES
	 */
	static bool mLoadedFlag;

public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	StaticInitializer()
	{
		load();
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~StaticInitializer()
	{
		dispose();
	}


public:
	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////

	static void load();

	static void dispose();

};



} /* namespace sep */
#endif /* STATIC_INITIALIZER_H_ */
