/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 8 juil. 2009
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef UTIL_BOOSTFACTORY_H_
#define UTIL_BOOSTFACTORY_H_

#include <string>

# if defined(BOOST_FILESYSTEM_VERSION) \
  && BOOST_FILESYSTEM_VERSION != 2  && BOOST_FILESYSTEM_VERSION != 3
#   error BOOST_FILESYSTEM_VERSION defined, but not as 2 or 3
# endif


namespace sep
{

class BoostFactory
{

public:
	static std::string PLATFORM;

	static bool IS_WINXX_PLATFORM;
	static bool IS_CYGWYN_PLATFORM;
	static bool IS_WINDOWS_PLATFORM;
	static bool IS_POSIX_PLATFORM;

};


}

#endif /* UTIL_BOOSTFACTORY_H_ */
