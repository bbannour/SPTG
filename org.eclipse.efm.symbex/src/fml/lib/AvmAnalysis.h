/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 25 juil. 2013
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVMANALYSIS_H_
#define AVMANALYSIS_H_

#include <string>


namespace sep
{


class STATIC_ANALYSIS
{

public:

	////////////////////////////////////////////////////////////////////////////////
	// VARIABLE_DEPENDENCY
	////////////////////////////////////////////////////////////////////////////////

	enum VARIABLE_DEPENDENCY_RING {
		UNDEFINED_DEPENDENCY,

		DEPENDENT,

		INDEPENDENT,

		UNKNOWN_DEPENDENCY
	};

	static std::string to_string(VARIABLE_DEPENDENCY_RING status);


};


} /* namespace sep */
#endif /* AVMANALYSIS_H_ */
