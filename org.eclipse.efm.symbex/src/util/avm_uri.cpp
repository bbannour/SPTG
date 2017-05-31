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

#include "avm_uri.h"

#include <fstream>

#include <util/avm_assert.h>


namespace sep
{


/**
 * open / close
 * OS
 */

bool AvmUri::open()
{
	if( outStream.good() )
	{
		return( true );
	}

	else switch ( kind )
	{
		case AVM_URI_STREAM_STD_COUT_KIND:
		{
			outStream.OS = AVM_OS_COUT.OS;

			break;
		}
		case AVM_URI_STREAM_STD_CERR_KIND:
		{
			outStream.OS = AVM_OS_CERR.OS;

			break;
		}


		case AVM_URI_STREAM_AVM_LOG_KIND:
		{
			outStream.OS = AVM_OS_LOG.OS;

			break;
		}

		case AVM_URI_STREAM_AVM_TRACE_KIND:
		{
			outStream.OS = AVM_OS_TRACE.OS;

			break;
		}

		case AVM_URI_FOLDER_KIND:
		{
			break;
		}

		case AVM_URI_FILE_KIND:
		case AVM_URI_FILENAME_KIND:
		{
			if( outStream.fail() )
			{
				if( outStream.open(location.c_str() , mode) )
				{
					isAllocated = true;
				}
				else
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Failed to open << " << location
							<< " >> file in write mode !!!"
							<< SEND_EXIT;
				}
			}

			break;
		}

		case AVM_URI_SOCKET_KIND:
		{
			outStream = NULL;

			break;
		}


		case AVM_URI_UNDEFINED_KIND:
		{
			outStream = NULL;

			break;
		}

		default:
		{
			outStream = NULL;

			break;
		}
	}

	return( true );
}


/**
 ***************************************************************************
 * SERIALIZATION
 ***************************************************************************
 */

std::string AvmUri::strKind(avm_uri_kind_t kind)
{
	switch ( kind )
	{
		case AVM_URI_STREAM_STD_COUT_KIND  : return( "stream:std:cout");
		case AVM_URI_STREAM_STD_CERR_KIND  : return( "stream:std:cerr");

		case AVM_URI_STREAM_AVM_LOG_KIND   : return( "stream:avm:log");
		case AVM_URI_STREAM_AVM_TRACE_KIND : return( "stream:avm:trace");

		case AVM_URI_FOLDER_KIND           : return( "folder");
		case AVM_URI_FILE_KIND             : return( "file");
		case AVM_URI_FILENAME_KIND         : return( "filename");

		case AVM_URI_SOCKET_KIND           : return( "socket");

		case AVM_URI_UNDEFINED_KIND        : return( "undefined<uri#kind>");

		default                            : return( "unknown<uri#kind>" );
	}
}


void AvmUri::toStream(OutStream & os) const
{
	os << TAB << "uri< " << strKind(kind) << " > {" << EOL;
	os << TAB2 << "raw = " << raw << ";" << EOL;
	os << TAB2 << "location = " << location << ";" << EOL;

	if( kind == AVM_URI_SOCKET_KIND )
	{
		os << TAB2 << "port = " << port << ";" << EOL;
	}
	os << TAB << "}" << EOL_FLUSH;
}

} /* namespace sep */
