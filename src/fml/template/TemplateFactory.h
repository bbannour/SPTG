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

#ifndef TEMPLATEFACTORY_H_
#define TEMPLATEFACTORY_H_

namespace sep
{

class Machine;


class TemplateFactory
{

public:
	static void genProperty(Machine * machine);

	static void genBehavior(Machine * machine);

};

} /* namespace sep */

#endif /* TEMPLATEFACTORY_H_ */
