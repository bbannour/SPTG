/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 2 juin 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef PRINTER_WRAPSTREAM_H_
#define PRINTER_WRAPSTREAM_H_

#include <iostream>
#include <string>

namespace sep
{


class WObject;


////////////////////////////////////////////////////////////////////////////////
// WrapData
////////////////////////////////////////////////////////////////////////////////

struct WrapData
{
	/**
	 * ATTRIBUTES
	 */
	std::size_t  LINE_WIDTH;

	std::size_t  INIT_WIDTH;

	std::size_t  TAB_WIDTH;

	std::string SEPARATOR;

	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WrapData(std::size_t lineWidth,
			std::size_t initWidth = 0, std::size_t tabWidth = 4,
			const std::string & wrapSeparator = "\n\t")
	: LINE_WIDTH( lineWidth ),
	INIT_WIDTH( initWidth ),
	TAB_WIDTH( tabWidth ),
	SEPARATOR( wrapSeparator )
	{
		//!! NOTHING
	}

	WrapData(std::size_t initWidth, const WrapData & aWrapData)
	: LINE_WIDTH( aWrapData.LINE_WIDTH ),
	INIT_WIDTH( initWidth ),
	TAB_WIDTH( aWrapData.TAB_WIDTH ),
	SEPARATOR( aWrapData.SEPARATOR )
	{
		//!! NOTHING
	}

	WrapData(const WrapData & aWrapData)
	: LINE_WIDTH( aWrapData.LINE_WIDTH ),
	INIT_WIDTH( aWrapData.INIT_WIDTH ),
	TAB_WIDTH( aWrapData.TAB_WIDTH ),
	SEPARATOR( aWrapData.SEPARATOR )
	{
		//!! NOTHING
	}


	bool configure(WObject * wfParameterObject);

};


extern WrapData DEFAULT_WRAP_DATA;


/**
 * Manipulators
 */
inline WrapData WRAP(std::size_t lineWidth,
		std::size_t initWidth = 0, std::size_t tabWidth = 4,
		const std::string & wrapSeparator = "\n\t")
{
	return( WrapData(lineWidth, initWidth, tabWidth, wrapSeparator) );
}

inline WrapData WRAP(std::size_t lineWidth,
		const std::string & wrapSeparator)
{
	return( WrapData(lineWidth, 0, 4, wrapSeparator) );
}


////////////////////////////////////////////////////////////////////////////////
// WrapStreambuf
////////////////////////////////////////////////////////////////////////////////

class WrapStreambuf  :  public std::streambuf
{

protected:
	/**
	 * TYPEDEF
	 */
	typedef std::basic_string<char_type>  string_type;

	/**
	 * ATTRIBUTE
	 */
	std::streambuf * mStreambuf;

	WrapData mWrapData;

	std::size_t mCharCount;

	string_type mBuffer;


public:
	/**
	 * CONSTRUCTORS
	 */
	WrapStreambuf(std::streambuf * buf, const WrapData & wrapData)
	: mStreambuf( buf ),
	mWrapData( wrapData ),
	mCharCount( wrapData.INIT_WIDTH ),
	mBuffer( )
	{
		//!! NOTHING
	}

	WrapStreambuf(std::streambuf * buf, std::size_t lineWidth,
			std::size_t initWidth = 0, std::size_t tabWidth = 4,
			const std::string & wrapSeparator = "\n\t")
	: mStreambuf( buf ),
	mWrapData( lineWidth, initWidth, tabWidth, wrapSeparator ),
	mCharCount( initWidth ),
	mBuffer( )
	{
		//!! NOTHING
	}

	/**
	 * DESTRUCTOR
	 */
	~WrapStreambuf()
	{
		flush();
	}

	/**
	 * flush()
	 */
	inline int_type flush() const
	{
		return( mStreambuf->sputn(mBuffer.c_str(), mBuffer.size()) );

	}

private:
	/**
	 * overflow(...)
	 */
	int_type overflow(int_type c);

};


////////////////////////////////////////////////////////////////////////////////
// WrapOstream
////////////////////////////////////////////////////////////////////////////////

class WrapOstream  :  public std::ostream
{

protected:
	/**
	 * ATTRIBUTE
	 */
	WrapStreambuf mWrapStreambuf;

public:
	std::ostream * mOS;

	/**
	 * CONSTRUCTORS
	 */
	WrapOstream(std::ostream & os, const WrapData & wrapData)
	: std::ostream( & mWrapStreambuf ),
	mWrapStreambuf( os.rdbuf(), wrapData ),
	mOS( & os )
	{
		//!! NOTHING
	}

	WrapOstream(std::ostream & os, std::size_t wrapWidth,
			std::size_t initialCharCount = 0,
			const std::string & wrapSeparator = "\n\t")
	: std::ostream( & mWrapStreambuf ),
	mWrapStreambuf( os.rdbuf(), wrapWidth,
			initialCharCount, 4, wrapSeparator ),
	mOS( & os )
	{
		//!! NOTHING
	}


	/**
	 * flush()
	 */
	inline void flush() const
	{
		mWrapStreambuf.flush();
	}

};


} /* namespace sep */

#endif /* PRINTER_WRAPSTREAM_H_ */
