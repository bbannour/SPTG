/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 21 mars 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef FML_COMMON_TRACEABLEELEMENT_H_
#define FML_COMMON_TRACEABLEELEMENT_H_

#include <string>

#include <common/Element.h>

#include <fml/common/LocationElement.h>


namespace sep
{

class TraceableElement
{

protected:
	/**
	 * ATTRIBUTES
	 */
	bool mCommentFlag;

	std::string mDescription;

	LocationElement * mLocation;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	TraceableElement()
	: mCommentFlag( false ),
	mDescription( ),
	mLocation( NULL )
	{
		//!! NOTHING
	}

	/**
	 * CONSTRUCTOR
	 * Copy
	 */
	TraceableElement(const TraceableElement & anElement)
	: mCommentFlag( anElement.mCommentFlag ),
	mDescription( anElement.mDescription),
	mLocation( (anElement.mLocation == NULL) ? NULL :
			new LocationElement( *(anElement.mLocation) ) )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~TraceableElement()
	{
		delete( mLocation );
	}


	/**
	 * GETTER - SETTER
	 * mCommentFlag
	 */
	inline bool isComment() const
	{
		return( mCommentFlag );
	}

	inline void setComment(bool isComment = true)
	{
		mCommentFlag = isComment;
	}


	/**
	 * GETTER - SETTER
	 * mDescription
	 */
	inline std::string getDescription() const
	{
		return( mDescription );
	}

	inline void setDescription(const std::string & aDescription)
	{
		mDescription = aDescription;
	}


	/**
	 * GETTER - SETTER
	 * mLocation
	 */
	inline LocationElement * getLocation() const
	{
		return( mLocation );
	}

	inline bool hasLocation() const
	{
		return( mLocation != NULL );
	}


	inline void setLocation(LocationElement * aLocation)
	{
		if( mLocation != NULL )
		{
			delete( mLocation );
		}
		mLocation = aLocation;
	}

	inline void copyLocation(LocationElement * aLocation)
	{
		if( aLocation != NULL )
		{
			setLocation(aLocation->getFileLocation(),
					aLocation->getBeginLine(), aLocation->getEndLine());
		}
		else if( mLocation != NULL )
		{
			delete( mLocation );
			mLocation = NULL;
		}
	}

	inline void setLocation(const std::string & aFileLocation,
			const avm_size_t beginLine, const avm_size_t endLine)
	{
		if( mLocation == NULL )
		{
			mLocation = new LocationElement(aFileLocation, beginLine, endLine);
		}
		else
		{
			mLocation->setLocation(aFileLocation, beginLine, endLine);
		}
	}


	/**
	 * FATAL ERROR location
	 */
	inline std::string fatalErrorLocation(
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->fatalErrorLocation() );
		}
		else if( container != NULL )
		{
			return( container->fatalErrorLocation(NULL) );
		}
		else
		{
			return( ":fatal error< location#undefined >\n\t" );
		}
	}

	inline OutStream & fatalErrorLocation(OutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->fatalErrorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->fatalErrorLocation(os, NULL) );
		}
		else
		{
			return( os << ":fatal error< location#undefined >\n\t" );
		}
	}

	inline PairOutStream & fatalErrorLocation(PairOutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->fatalErrorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->fatalErrorLocation(os, NULL) );
		}
		else
		{
			return( os << ":fatal error< location#undefined >\n\t" );
		}
	}

	inline TripleOutStream & fatalErrorLocation(TripleOutStream & os,
			TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->fatalErrorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->fatalErrorLocation(os, NULL) );
		}
		else
		{
			return( os << ":fatal error< location#undefined >\n\t" );
		}
	}


	/**
	 * ERROR location
	 */
	inline std::string errorLocation(
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->errorLocation() );
		}
		else if( container != NULL )
		{
			return( container->errorLocation(NULL) );
		}
		else
		{
			return( ":error< location#undefined >\n\t" );
		}
	}

	inline OutStream & errorLocation(OutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->errorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->errorLocation(os, NULL) );
		}
		else
		{
			return( os << ":error< location#undefined >\n\t" );
		}
	}

	inline PairOutStream & errorLocation(PairOutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->errorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->errorLocation(os, NULL) );
		}
		else
		{
			return( os << ":error< location#undefined >\n\t" );
		}
	}

	inline TripleOutStream & errorLocation(TripleOutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->errorLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->errorLocation(os, NULL) );
		}
		else
		{
			return( os << ":error< location#undefined >\n\t" );
		}
	}


	/**
	 * WARNING location
	 */
	inline std::string warningLocation(
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->warningLocation() );
		}
		else if( container != NULL )
		{
			return( container->warningLocation(NULL) );
		}
		else
		{
			return( ":warning< location#undefined >\n\t" );
		}
	}

	inline OutStream & warningLocation(OutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->warningLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->warningLocation(os, NULL) );
		}
		else
		{
			return( os << ":warning< location#undefined >\n\t" );
		}
	}

	inline PairOutStream & warningLocation(PairOutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->warningLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->warningLocation(os, NULL) );
		}
		else
		{
			return( os << ":warning< location#undefined >\n\t" );
		}
	}

	inline TripleOutStream & warningLocation(TripleOutStream & os,
			const TraceableElement * container = NULL) const
	{
		if( mLocation != NULL )
		{
			return( mLocation->warningLocation(os) );
		}
		else if( container != NULL )
		{
			return( container->warningLocation(os, NULL) );
		}
		else
		{
			return( os << ":warning< location#undefined >\n\t" );
		}
	}

	/**
	 * traceLine info
	 */
	inline std::string traceLine(const std::string & tab,
			bool singleLineComment = true) const
	{
		return( (mLocation != NULL ) ?
				mLocation->traceLine(tab, singleLineComment) : "" );
	}

};

} /* namespace sep */

#endif /* FML_COMMON_TRACEABLEELEMENT_H_ */
