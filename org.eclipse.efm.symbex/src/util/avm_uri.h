/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 23 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#ifndef AVM_URI_H_
#define AVM_URI_H_

#include <printer/OutStream.h>

#include <util/avm_numeric.h>


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// The URI KIND
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

typedef avm_uint8_t         avm_uri_kind_t;

enum {
	AVM_URI_UNDEFINED_KIND         = 0x0000,

	AVM_URI_STREAM_STD_COUT_KIND   = 0x0001,
	AVM_URI_STREAM_STD_CERR_KIND   = 0x0002,

	AVM_URI_STREAM_AVM_LOG_KIND    = 0x0004,
	AVM_URI_STREAM_AVM_TRACE_KIND  = 0x0008,

	AVM_URI_FOLDER_KIND            = 0x0010,
	AVM_URI_FILE_KIND              = 0x0020,
	AVM_URI_FILENAME_KIND          = 0x0040,

	AVM_URI_SOCKET_KIND            = 0x0080
};

#define IS_URI_UNDEFINED(kind)              (kind == AVM_URI_UNDEFINED_KIND)

#define IS_URI_STREAM_STD_COUT_KIND(kind)   (kind & AVM_URI_STREAM_STD_COUT_KIND)
#define IS_URI_STREAM_STD_CERR_KIND(kind)   (kind & AVM_URI_STREAM_STD_CERR_KIND)

#define IS_URI_STREAM_AVM_LOG_KIND(kind)    (kind & AVM_URI_STREAM_AVM_LOG_KIND)
#define IS_URI_STREAM_AVM_TRACE_KIND(kind)  (kind & AVM_URI_STREAM_AVM_TRACE_KIND)

#define IS_URI_FOLDER_KIND(kind)            (kind & AVM_URI_FOLDER_KIND)
#define IS_URI_FILE_KIND(kind)              (kind & AVM_URI_FILE_KIND)
#define IS_URI_FILENAME_KIND(kind)          (kind & AVM_URI_FILENAME_KIND)

#define IS_URI_SOCKET_KIND(kind)            (kind & AVM_URI_SOCKET_KIND)



class AvmUri
{

public:
	/**
	 * ATTRIBUTES
	 */
	std::string    raw;

	avm_uri_kind_t kind;

	std::string    location;

	avm_uint64_t   port;

	OutStream outStream;
	std::ios_base::openmode mode;

	bool isAllocated;


public:
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	AvmUri( const std::string & rawLocation )
	: raw( rawLocation ),
	kind( AVM_URI_UNDEFINED_KIND ),
	location( ),
	port( 0 ),
	outStream( ),
	mode( std::ios_base::out ),
	isAllocated( false )
	{
		//!! NOTHING
	}

	AvmUri( avm_uri_kind_t aKind, const std::string & rawLocation )
	: raw( rawLocation ),
	kind( aKind ),
	location( ),
	port( 0 ),
	outStream( ),
	mode( std::ios_base::out ),
	isAllocated( false )
	{
		//!! NOTHING
	}


	/**
	 * DESTRUCTOR
	 */
	virtual ~AvmUri()
	{
		//!! NOTHING
	}


	/**
	 * COMPARISON
	 * OPERATOR
	 */

	inline bool operator==(const AvmUri & uri) const
	{
		return( (raw == uri.raw) && (kind == uri.kind) &&
				(location == uri.location) && (port == uri.port) );
	}


	/**
	 * open / close
	 * OS
	 */

	bool open();

	void close()
	{
		if( isAllocated )
		{
			outStream.deleteOS();
		}
	}

	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	static std::string strKind(avm_uri_kind_t kind);


	void toStream(OutStream & os) const;

};



} /* namespace sep */
#endif /* AVM_URI_H_ */
