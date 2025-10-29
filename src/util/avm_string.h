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

#ifndef AVM_STRING_H_
#define AVM_STRING_H_

#include <algorithm>
#include <sstream>
#include <string>

//#include <boost/algorithm/string.hpp>
//#include <boost/tokenizer.hpp>


namespace sep
{

#define SPACE_CHARS     " \t\f\v\n\r"


#define QUOTEME( X )  #X


#define STRIML(s)  s.substr(s.find_first_not_of(SPACE_CHARS))

#define STRIMR(s)  s.substr(0, s.find_last_not_of(SPACE_CHARS))

#define STRIM(s)   s.substr(s.find_first_not_of(SPACE_CHARS),  \
		s.find_last_not_of(SPACE_CHARS))


/**
 * REGEX
 * CONSTRUCTORS
 */
#define WID_SEPARATOR              "[^a-zA-Z\\s0-9]?"

#define CONS_WID2(w1, w2)          w1  WID_SEPARATOR  w2

#define CONS_WID3(w1, w2, w3)      w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3

#define PLUS_WID3(w1, w2, w3)      \
	(std::string(w1) + WID_SEPARATOR + w2 + WID_SEPARATOR + w3)

#define CONS_WID4(w1, w2, w3, w4)  \
	w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3  WID_SEPARATOR  w4

#define CONS_WID5(w1, w2, w3, w4, w5)  \
	w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3  WID_SEPARATOR  w4  WID_SEPARATOR  w5

#define CONS_WID6(w1, w2, w3, w4, w5, w6)  \
	w1  WID_SEPARATOR  w2  WID_SEPARATOR  w3  WID_SEPARATOR  w4  WID_SEPARATOR  w5  WID_SEPARATOR  w6


#define PREFIX_WID(w1, w2)          "(" w1  WID_SEPARATOR ")?(" w2 ")"

#define SUFFIX_WID(w1, w2)          "(" w1 ")(" WID_SEPARATOR  w2 ")?"


#define OP_OR 					 "|"

#define OR_WID2(w1, w2)          w1  OP_OR  w2

#define OR_WID3(w1, w2, w3)      w1  OP_OR  w2  OP_OR  w3

#define OR_WID4(w1, w2, w3, w4)  w1  OP_OR  w2  OP_OR  w3  OP_OR  w4



// Conversion
template< typename T >
T string_to(const std::string & strInput,
		std::ios_base & (*f)(std::ios_base &) = std::dec)
{
	std::istringstream iss(strInput);
	T t;

	if( ( iss >> f >> t ).fail() )
	{
//		AVM_OS_FATAL_ERROR_EXIT
//				<< "fail:> sep::string_to< T >( " << aValue << " ) !!!"
//				<< SEND_EXIT;
	}

	return( t );
}

template< typename T >
bool from_string(const std::string & strInput, T & t,
		std::ios_base & (*f)(std::ios_base &) = std::dec)
{
	std::istringstream iss(strInput);

	return( not ( iss >> f >> t ).fail() );
}

template< typename T , typename U >
bool from_string(const std::string & strInput, T & t, char separator,
		U & u, std::ios_base & (*f)(std::ios_base &) = std::dec)
{
	std::istringstream iss(strInput);

	char c;

	return( (not ( iss >> f >> t >> c >> f >> u ).fail()) &&
			(c == separator) );
}


template< typename T >
std::string to_string( const T & a )
{
	std::ostringstream oss;
	oss << a;
	return oss.str();
}


/**
 * TOOLS / UTILS
 */
class StringTools
{

public:

	////////////////////////////////////////////////////////////////////////////
	// TOLOWER -- TOUPPER
	////////////////////////////////////////////////////////////////////////////

	inline static void tolower(std::string & str)
	{
		std::transform(str.begin(), str.end(), str.begin(), ::tolower );
	}

	inline static void toupper(std::string & str)
	{
		std::transform(str.begin(), str.end(), str.begin(), ::toupper );
	}


	////////////////////////////////////////////////////////////////////////////
	// STRING SPLIT
	////////////////////////////////////////////////////////////////////////////

//	static std::vector<std::string> string_split(
//			std::string s, const char delimiter);

	static std::string string_split(
			std::string s, const char delimiter, unsigned int occurence);

	////////////////////////////////////////////////////////////////////////////
	// REGEX MATCH TEXT
	////////////////////////////////////////////////////////////////////////////

	static bool regex_match(
			const std::string & text, const std::string & regex);

#define REGEX_MATCH( text , regex )  StringTools::regex_match( text , regex )

	static bool regex_find(
			const std::string & text, const std::string & regex);

#define REGEX_FIND( text , regex )   StringTools::regex_find( text , regex )


	static bool regex_startsWith(
			const std::string & text, const std::string & regex);

#define REGEX_STARTS( text , regex )  \
			StringTools::regex_startsWith( text , regex )

	static bool regex_endsWith(
			const std::string & text, const std::string & regex);

#define REGEX_ENDS( text , regex )   \
			StringTools::regex_endsWith( text , regex )


	////////////////////////////////////////////////////////////////////////////
	// REPLACE TEXT
	////////////////////////////////////////////////////////////////////////////

	static void replace(std::string & mainStr, const std::string & patternA,
			const std::string & patternB);

	static void replaceAll(std::string & mainStr, const std::string & patternA,
			const std::string & patternB);

	static void replaceAllEscapeSequences(std::string & mainStr);


	static std::string regex_replace(const std::string & mainStr,
			const std::string & regex_pattern, const std::string & pattern);



	////////////////////////////////////////////////////////////////////////////
	// ERASE TEXT
	////////////////////////////////////////////////////////////////////////////

	static void erase(std::string & mainStr, const std::string & pattern);

	static void eraseAll(std::string & mainStr, const std::string & pattern);


	////////////////////////////////////////////////////////////////////////////
	// STARTS , ENDS  WITH
	////////////////////////////////////////////////////////////////////////////

//	inline static bool startsWith(
//			const std::string & strA, const std::string & strB)
//	{
//		std::string::size_type sizeB = strB.size();
//
//		return( (strA.size() >= sizeB)
//				&& (strA.compare(0, sizeB, strB) == 0) );
//
////		return( (strA.size() >= strB.size()) &&
////				std::equal(strB.begin(), strB.end(), strA.begin()) );
//	}

	inline static bool stricklyStartsWith(
			const std::string & strA, const std::string & strB)
	{
		std::string::size_type sizeB = strB.size();

		return( (strA.size() > sizeB)
				&& (strA.compare(0, sizeB, strB) == 0) );
	}

//	inline static bool endsWith(
//			const std::string & strA, const std::string & strB)
//	{
//		std::string::size_type sizeA = strA.size();
//		std::string::size_type sizeB = strB.size();
//
//		return( (sizeA >= sizeB)
//				&& (strA.compare(sizeA - sizeB, sizeB, strB) == 0) );
//
////		return( (strA.size() >= strB.size()) &&
////				std::equal(strB.rbegin(), strB.rend(), strA.rbegin()) );
//	}

	inline static std::string removeLastIfEndsWith(
			const std::string & strA, const std::string & strB)
	{
		std::string::size_type sizeA = strA.size();
		std::string::size_type sizeB = strB.size();

		if( (sizeA >= sizeB)
			&& (strA.compare(sizeA - sizeB, sizeB, strB) == 0) )
		{
			return( strA.substr(0, sizeA - sizeB) );
		}
		else
		{
			return( strA );
		}
	}



	////////////////////////////////////////////////////////////////////////////
	// TRIM LEFT RIGHT
	////////////////////////////////////////////////////////////////////////////

	// trim from start to first_not_of(SPACE_CHARS) + pos
	inline static std::string & ltrim(
			std::string & s, std::string::size_type pos = 0)
	{
//		boost::algorithm::trim_left( s );
		s.erase(0, s.find_first_not_of(SPACE_CHARS, pos));

		return( s );
	}

	// trim from end
	inline static std::string & rtrim(std::string & s)
	{
//		boost::algorithm::trim_right( s );
		s.erase(s.find_last_not_of(SPACE_CHARS) + 1);

		return( s );
	}

	// trim from both ends
	inline static std::string & trim(std::string & s)
	{
//		boost::algorithm::trim( s );

//		return( s );

		return( ltrim( rtrim(s) ) );
	}


	////////////////////////////////////////////////////////////////////////////
	// TOKEN PARSER
	////////////////////////////////////////////////////////////////////////////

	inline static bool nextToken(std::string & buffer,
			std::string & token, const std::string & separator = SPACE_CHARS)
	{
		// token position: 0 --> pos
		std::string::size_type pos = buffer.find_first_of(separator);

		// next token
		token = buffer.substr(0, pos);

		// updated buffer
		buffer.erase(0, buffer.find_first_not_of(SPACE_CHARS, pos));

		return( not token.empty() );
	}

	inline static bool nextTokenWord(std::string & buffer,
			std::string & token, const std::string & expectdWord)
	{
		if( buffer.size() < expectdWord.size() )
		{
			return( false );
		}
		else
		{
			std::string::size_type pos = 0;

			for( ; pos < expectdWord.size() ; ++pos )
			{
				if( buffer[pos] != expectdWord[pos] )
				{
					return( false );
				}
			}

			// next token
			token = expectdWord;

			// updated buffer
			buffer.erase(0, buffer.find_first_not_of(SPACE_CHARS, pos));

			return( true );
		}
	}


	inline static bool nextTokenID(std::string & buffer,
			std::string & token, const std::string & separator = SPACE_CHARS)
	{
		// ID position: 0 --> pos
		std::string::size_type pos = 0;
		if( std::isalpha(buffer[0]) || (buffer[0] == '_') || (buffer[0] == '#') )
		{
			for( ++pos ; (pos < buffer.size()) && (std::isalnum(buffer[pos]) ||
				(buffer[pos] == '_') || (buffer[pos] == '#')) ; ++pos )
			{
				//!! CONTINUE
			}
		}

		// next token
		token = buffer.substr(0, pos);

		// updated buffer
		buffer.erase(0, buffer.find_first_not_of(separator, pos));

		return( not token.empty() );
	}


	inline static bool nextTokenUFID(std::string & buffer,
			std::string & token, const std::string & separator = SPACE_CHARS)
	{
		// ID position: 0 --> pos
		std::string::size_type pos = 0;
		if( std::isalpha(buffer[0])
			|| (buffer[0] == '_')
			|| (buffer[0] == '#')
			|| (buffer[pos] == ':') )
		{
			for( ++pos ; (pos < buffer.size()) &&
				( std::isalnum(buffer[pos])
				|| (buffer[pos] == '_')
				|| (buffer[pos] == '#')
				|| (buffer[pos] == '.')
				|| (buffer[pos] == ':') ) ; ++pos )
			{
				//!! CONTINUE
			}
		}

		// next token
		token = buffer.substr(0, pos);

		// updated buffer
		buffer.erase(0, buffer.find_first_not_of(separator, pos));

		return( not token.empty() );
	}

};


}

#endif /* AVM_STRING_H_ */
