/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 18 sept. 2008
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef LOCATIONELEMENT_H_
#define LOCATIONELEMENT_H_

#include <printer/OutStream.h>


namespace sep
{


class LocationElement
{

protected:
	/**
	 * ATTRIBUTES
	 */
	static std::string mLastReportFileLocation;

	std::string mFileLocation;

	std::size_t mBeginLine;

	std::size_t mEndLine;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	LocationElement()
	: mFileLocation( ),
	mBeginLine( 0 ),
	mEndLine( 0 )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	LocationElement(const LocationElement & anElement)
	: mFileLocation( anElement.mFileLocation ),
	mBeginLine( anElement.mBeginLine ),
	mEndLine( anElement.mEndLine )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 * Other
	 */
	LocationElement(const std::string & aFileLocation,
			const std::size_t aBeginLine, const std::size_t anEndLine)
	: mFileLocation( aFileLocation ),
	mBeginLine( aBeginLine ),
	mEndLine( anEndLine )
	{
		//!! NOTHING
	}

	LocationElement(const std::string & aFileLocation, const std::size_t aLine)
	: mFileLocation( aFileLocation ),
	mBeginLine( aLine ),
	mEndLine( aLine )
	{
		//!! NOTHING
	}

	LocationElement(const std::size_t aBeginLine, const std::size_t anEndLine)
	: mFileLocation( ),
	mBeginLine( aBeginLine ),
	mEndLine( anEndLine )
	{
		//!! NOTHING
	}

	LocationElement(const std::size_t aLine)
	: mFileLocation( ),
	mBeginLine( aLine ),
	mEndLine( aLine )
	{
		//!! NOTHING
	}


	/**
	 * CONSTRUCTOR
	 */
	virtual ~LocationElement()
	{
		//!! NOTHING
	}


	/**
	 * GETTER - SETTER
	 * mFileLocation
	 */
	inline const std::string & getFileLocation() const
	{
		return( mFileLocation );
	}

	inline bool hasFileLocation() const
	{
		return( ! (mFileLocation.empty()) );
	}

	inline void setFileLocation(const std::string & aFileLocation)
	{
		mFileLocation = aFileLocation;
	}


	inline OutStream & reportFileLocation(OutStream & os) const
	{
//	    if( mFileLocation != mLastReportFileLocation )
//	    {
//			os << mFileLocation std::endl;
//
//			mLastReportFileLocation = mFileLocation;
//	    }

		os << mFileLocation << ":";

		return( os );
	}

	inline PairOutStream & reportFileLocation(PairOutStream & os) const
	{
//	    if( mFileLocation != mLastReportFileLocation )
//	    {
//			os << mFileLocation std::endl;
//
//			mLastReportFileLocation = mFileLocation;
//	    }

		os << mFileLocation << ":";

		return( os );
	}

	inline TripleOutStream & reportFileLocation(TripleOutStream & os) const
	{
//		if( mFileLocation != mLastReportFileLocation )
//		{
//			os << mFileLocation std::endl;
//
//			mLastReportFileLocation = mFileLocation;
//		}

		os << mFileLocation << ":";

		return( os );
	}



	/**
	 * GETTER - SETTER
	 * mBeginLine
	 */
	inline std::size_t getBeginLine() const
	{
		return( mBeginLine );
	}

	inline bool hasBeginLine() const
	{
		return( mBeginLine > 0 );
	}

	inline void setBeginLine(const std::size_t aBeginLine)
	{
		mBeginLine = aBeginLine;
	}


	/**
	 * GETTER - SETTER
	 * mEndLine
	 */
	inline std::size_t getEndLine() const
	{
		return( mEndLine );
	}

	inline bool hasEndLine() const
	{
		return( mEndLine > 0 );
	}

	inline void setEndLine(const std::size_t anEndLine)
	{
		mEndLine = anEndLine;
	}


	/**
	 * SETTER
	 * mFileLocation
	 * mBeginLine
	 * mEndLine
	 */
	inline void setLocation(const LocationElement & anElement)
	{
		mFileLocation = anElement.mFileLocation;

		mBeginLine = anElement.mBeginLine;
		mEndLine   = anElement.mEndLine;
	}

	inline void setLocation(const std::string & aFileLocation,
			const std::size_t aBeginLine, const std::size_t anEndLine)
	{
		mFileLocation = aFileLocation;

		mBeginLine = aBeginLine;
		mEndLine   = anEndLine;
	}

	inline void setLocation(const std::string & aFileLocation,
			const std::size_t aLine)
	{
		mFileLocation = aFileLocation;

		mEndLine = mBeginLine = aLine;
	}


	inline void setLine(const std::size_t aBeginLine, const std::size_t anEndLine)
	{
		mBeginLine = aBeginLine;
		mEndLine   = anEndLine;
	}

	inline void setLine(const std::size_t aLine)
	{
		mEndLine = mBeginLine = aLine;
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	inline std::string strLine() const
	{
		std::ostringstream oss;

		if( mBeginLine != mEndLine )
		{
			oss << /*"line " <<*/ mBeginLine << " -> " << mEndLine;
		}
		else
		{
			oss << /*"line " <<*/ mBeginLine;
		}

		return( oss.str() );
	}


	inline std::string traceLine(
			const std::string tab, bool singleLineComment = true) const
	{
		std::ostringstream oss(tab);

		if( singleLineComment )
		{
			oss << "// " << strLine();
		}
		else
		{
			oss << "/*" << strLine() << "*/";
		}

		return( oss.str() );
	}


	inline std::string fatalErrorLocation() const
	{
		StringOutStream oss;

		fatalErrorLocation(oss);

		return( oss.str() );
	}

	inline OutStream & fatalErrorLocation(OutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Fatal error:> " << std::flush;

		return( os );
	}

	inline PairOutStream & fatalErrorLocation(PairOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Fatal error:> " << std::flush;

		return( os );
	}

	inline TripleOutStream & fatalErrorLocation(TripleOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Fatal error:> " << std::flush;

		return( os );
	}


	inline std::string errorLocation() const
	{
		StringOutStream oss;

		errorLocation(oss);

		return( oss.str() );
	}

	inline OutStream & errorLocation(OutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Error:> " << std::flush;

		return( os );
	}

	inline PairOutStream & errorLocation(PairOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Error:> " << std::flush;

		return( os );
	}

	inline TripleOutStream & errorLocation(TripleOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Error:> " << std::flush;

		return( os );
	}


	inline std::string warningLocation() const
	{
		StringOutStream oss;

		warningLocation(oss);

		return( oss.str() );
	}

	inline OutStream & warningLocation(OutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Warning:> " << std::flush;

		return( os );
	}

	inline PairOutStream & warningLocation(PairOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Warning:> " << std::flush;

		return( os );
	}

	inline TripleOutStream & warningLocation(TripleOutStream & os) const
	{
		reportFileLocation(os)
				<< strLine() << EOL_TAB << "Warning:> " << std::flush;

		return( os );
	}

};


}

#endif /* LOCATIONELEMENT_H_ */
