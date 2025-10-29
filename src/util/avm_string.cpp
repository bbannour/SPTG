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

#include <cstddef>
#include <regex>


namespace sep {


////////////////////////////////////////////////////////////////////////////
// STRING SPLIT
////////////////////////////////////////////////////////////////////////////

//std::vector<std::string> StringTools::string_split(
//		std::string s, const char delimiter)
//{
//	std::size_t start = 0;
//	std::size_t end = s.find_first_of(delimiter);
//
//    std::vector<std::string> output;
//
//    while (end <= std::string::npos)
//    {
//	    output.emplace_back(s.substr(start, end-start));
//
//	    if (end == std::string::npos)
//	    {
//	    	break;
//	    }
//
//    	start = end + 1;
//    	end = s.find_first_of(delimiter, start);
//    }
//
//    return output;
//}

std::string StringTools::string_split(
		std::string s, const char delimiter, unsigned int occurence)
{
	std::size_t start = 0;
	std::size_t end = s.find_first_of(delimiter);

    std::string output;

    for( unsigned int count = 1 ; (end <= std::string::npos) ; ++count )
    {
    	if( count == occurence )
    	{
    		output = s.substr(start, end-start);

    		break;
    	}

    	if (end == std::string::npos)
    	{
    		break;
    	}

    	start = end + 1;
    	end = s.find_first_of(delimiter, start);
    }

    return output;
}


////////////////////////////////////////////////////////////////////////////
// REGEX MATCH TEXT
////////////////////////////////////////////////////////////////////////////

bool StringTools::regex_match(
		const std::string & text, const std::string & regex)
{
	return( std::regex_match(text, std::regex(regex)) );
}

bool StringTools::regex_find(
		const std::string & text, const std::string & regex)
{
	return( std::regex_search(text, std::regex(regex)) );
}

bool StringTools::regex_startsWith(
		const std::string & text, const std::string & regex)
{
	return( std::regex_search(text, std::regex(regex),
			std::regex_constants::match_continuous) );
}

bool StringTools::regex_endsWith(
		const std::string & text, const std::string & regex)
{
	return( std::regex_match(text, std::regex(".*" + regex)) );
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

void StringTools::replaceAllEscapeSequences(std::string & mainStr)
{
	boost::replace_all(mainStr, "\\t" , "\t");
	boost::replace_all(mainStr, "\\n" , "\n");
	boost::replace_all(mainStr, "\\\"", "\"");
}

std::string StringTools::regex_replace(const std::string & mainStr,
		const std::string & regex_pattern, const std::string & pattern)
{
	return( std::regex_replace(mainStr, std::regex(regex_pattern), pattern) );
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
