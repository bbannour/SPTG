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

#include "BoostFactory.h"

#include <boost/config.hpp>


namespace sep
{


// BOOST_POSIX or BOOST_WINDOWS specify which API to use.
#if !defined( BOOST_WINXX ) || !defined( BOOST_WINDOWS ) && !defined( BOOST_POSIX ) && !defined( BOOST_CYGWIN )
#	if defined(WIN32) || defined(_WIN32) || defined(__WIN32__) || defined(WIN64) || defined(_WIN64) || defined(__WIN64__)
#		define __AVM_BOOST_WINXX__
#		define __AVM_BOOST_WINDOWS__
#	elif defined(CYGWIN) || defined(_CYGWIN) || defined(_CYGWIN_) || defined(__CYGWIN__)
#		define __AVM_BOOST_CYGWIN__
#		define __AVM_BOOST_WINDOWS__
#	else
#		define __AVM_BOOST_POSIX__
#	endif
#endif


std::string BoostFactory::PLATFORM = BOOST_PLATFORM;

bool BoostFactory::IS_WINXX_PLATFORM = (
		(BoostFactory::PLATFORM == "Win32") ||
		(BoostFactory::PLATFORM == "Win64") );


bool BoostFactory::IS_CYGWYN_PLATFORM  = (BoostFactory::PLATFORM == "Cygwin") ;


bool BoostFactory::IS_WINDOWS_PLATFORM = (
		BoostFactory::IS_WINXX_PLATFORM ||
		BoostFactory::IS_CYGWYN_PLATFORM );


bool BoostFactory::IS_POSIX_PLATFORM = (not BoostFactory::IS_WINDOWS_PLATFORM);


}
