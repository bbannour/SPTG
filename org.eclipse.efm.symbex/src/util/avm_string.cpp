/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 avr. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "avm_string.h"

#include <boost/algorithm/string.hpp>
#include <boost/regex.hpp>


namespace sep {


////////////////////////////////////////////////////////////////////////////
// REGEX MATCH TEXT
////////////////////////////////////////////////////////////////////////////

bool StringTools::regex_match(
		const std::string & text, const std::string & regex)
{
	return( boost::regex_match(text, boost::regex(regex)) );
}

bool StringTools::regex_find(
		const std::string & text, const std::string & regex)
{
	return( boost::regex_match(text, boost::regex(".*" + regex + ".*")) );
}

bool StringTools::regex_startsWith(
		const std::string & text, const std::string & regex)
{
	return( boost::regex_match(text, boost::regex(regex + ".*")) );
}

bool StringTools::regex_endsWith(
		const std::string & text, const std::string & regex)
{
	return( boost::regex_match(text, boost::regex(".*" + regex)) );
}


////////////////////////////////////////////////////////////////////////////////
// REPLACE TEXT
////////////////////////////////////////////////////////////////////////////////

void StringTools::replace(std::string & mainStr,
		const std::string & patternA, const std::string & patternB)
{
	boost::replace_first(mainStr, patternA, patternB);
}

void StringTools::replaceAll(std::string & mainStr,
		const std::string & patternA, const std::string & patternB)
{
	boost::replace_all(mainStr, patternA, patternB);
}

std::string regex_replace(const std::string & mainStr,
		const std::string & regex_pattern, const std::string & pattern)
{
	boost::regex re( regex_pattern );

	return( boost::regex_replace(mainStr, boost::regex(regex_pattern), pattern) );
}


////////////////////////////////////////////////////////////////////////////////
// ERASE TEXT
////////////////////////////////////////////////////////////////////////////////

void StringTools::erase(std::string & mainStr, const std::string & pattern)
{
	boost::erase_first(mainStr, pattern);
}

void StringTools::eraseAll(std::string & mainStr, const std::string & pattern)
{
	boost::erase_all(mainStr, pattern);
}


}
