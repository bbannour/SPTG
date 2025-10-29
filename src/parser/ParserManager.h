/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#ifndef PARSER_PARSERMANAGER_H_
#define PARSER_PARSERMANAGER_H_

#include <iosfwd>
#include <string>



namespace sep
{

class System;

class WObject;
class WObjectManager;


class ParserManager
{

protected:
	/**
	 * ATTRIBUTE
	 */
	std::string mFileLocation;
	std::string mFilename;

	std::size_t mErrorCount;

	std::size_t mWarningCount;

	std::string mExceptionMessage;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	ParserManager(const std::string & fileLocation);

	/**
	 * DESTRUCTOR
	 */
	virtual ~ParserManager()
	{
		//!! NOTHING
	}


	/**
	 * mErrorCount
	 */
	inline std::size_t getErrorCount() const
	{
		return( mErrorCount );
	}

	inline bool hasSyntaxError() const
	{
		return( mErrorCount > 0 );
	}

	inline bool hasNoSyntaxError() const
	{
		return( mErrorCount == 0 );
	}

	/**
	 * mWarningCount
	 */
	inline std::size_t getWarningCount() const
	{
		return( mWarningCount );
	}

	inline bool hasSyntaxWarning() const
	{
		return( mWarningCount > 0 );
	}


	/**
	 * mWarningCount
	 */
	inline const std::string & getExceptionMessage() const
	{
		return( mExceptionMessage );
	}

	inline bool hasExceptionMessage() const
	{
		return( not mExceptionMessage.empty() );
	}


	/**
	 * Parse FML, xLIA
	 */
	System * parseFML(WObjectManager & aWObjectManager);

	System * parseFML_ANTLR3(WObjectManager & aWObjectManager,
			std::istream & anInputStream);

	System * parseFML(WObjectManager & aWObjectManager,
			std::istream & anInputStream);

	/**
	 * Parse SEW, FAVM
	 */

	WObject * parseSEW(WObjectManager & aWObjectManager,
			std::istream & anInputStream);

};


}

#endif /*PARSER_PARSERMANAGER_H_*/
