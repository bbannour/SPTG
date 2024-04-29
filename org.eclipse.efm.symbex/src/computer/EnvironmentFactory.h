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

#ifndef ENVIRONMENTFACTORY_H_
#define ENVIRONMENTFACTORY_H_

namespace sep
{


class EnvironmentFactory
{

public:
	////////////////////////////////////////////////////////////////////////////
	// LOADER / DISPOSER  API
	////////////////////////////////////////////////////////////////////////////
	static void load();
	static void dispose();

};

} /* namespace sep */
#endif /* ENVIRONMENTFACTORY_H_ */
