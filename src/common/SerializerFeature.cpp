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

#include "SerializerFeature.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <util/avm_vfs.h>

#include <boost/tokenizer.hpp>


namespace sep
{

/**
 *******************************************************************************
prototype filter::filter_ufid as avm::core.filter.filter_type is
	section PROPERTY
		...
	endsection PROPERTY

	section REPORT
		@uri = std      ":" ( "cout" | "cerr"  )
		     | avm      ":" ( "log"  | "trace" )
		     | folder   ":" path
		     | file     ":" path
		     | filename ":" path
		     | socket   ":" host ":" port
		     ;
		@uri = ...;

		@when = [ init ][:]
		        [ otf | (every | after | before) ? value#unit][:][ exit ];

	endsection REPORT

endprototype
 *******************************************************************************

vfs [
	folder = "uri:acsl"
	file#1   = "acslSpec.h"

	file#2   = "acslSpec.cpp"

] // end vfs

 */


static bool scanPeriod(std::string period,
		avm_delay_value_t & value, avm_unit_t & unit)
{
	if( ::isdigit(period[0]) )
	{
		std::string::size_type pos = period.find('#');

		if( pos != std::string::npos )
		{
			if( not sep::from_string<avm_delay_value_t>(
					period.substr(0, pos), value, std::dec) )
			{
				return false;
			}
			period = period.substr(pos+1);

			if( period == "ns" )
			{
				unit = AVM_NANO_SECOND_UNIT;
			}
			else if( period == "µs" )
			{
				unit = AVM_MICRO_SECOND_UNIT;
			}
			else if( period == "ms" )
			{
				unit = AVM_MILLI_SECOND_UNIT;
			}
			else if( period == "s" )
			{
				unit = AVM_SECOND_UNIT;
			}
			else if( period == "min" )
			{
				unit = AVM_MINUTE_UNIT;
			}
			else if( period == "h" )
			{
				unit = AVM_HOUR_UNIT;
			}
			else if( period == "step" )
			{
				unit = AVM_STEP_UNIT;
			}
			else if( REGEX_MATCH(period , CONS_WID2("micro", "step")) )
			{
				unit = AVM_MICRO_STEP_UNIT;
			}
			else if( REGEX_MATCH(period , CONS_WID2("macro", "step")) )
			{
				unit = AVM_MACRO_STEP_UNIT;
			}
			else
			{
				return false;
			}

			return true;
		}
	}

	return false;
}

bool SerializerFeature::configure(const WObject * wfParameterObject)
{
	bool isConfigOK = true;

	const WObject * theVFS = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("vfs", "VFS"));

	if( theVFS == WObject::_NULL_ )
	{
		theVFS = Query::getRegexWSequence(
				wfParameterObject, OR_WID2("report", "REPORT"));
	}

	if( theVFS != WObject::_NULL_ )
	{
		mAutoOpenFileFlag =
				Query::getWPropertyBoolean(theVFS,
						CONS_WID3("auto", "open" ,"file"), mAutoOpenFileFlag);

		mReportDetailsFlag =
				Query::getWPropertyBoolean(theVFS, "details", mReportDetailsFlag);

		////////////////////////////////////////////////////////////////////////
		// The report mTableOfURI Attributes
		////////////////////////////////////////////////////////////////////////
		lastFolder.location = VFS::ProjectOutputPath;

		std::string::size_type pos;
		std::string scheme;
		std::string mode;
		std::string attrID;

		WObject::const_iterator itWfO = theVFS->owned_begin();
		WObject::const_iterator endWfO = theVFS->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				scheme = attrID = (*itWfO)->getNameID();

				AvmUri & uri = appendUri( attrID , (*itWfO)->toStringValue() );

				if( scheme.starts_with("uri") )
				{
					pos = uri.raw.find_first_of(":#");
					if( pos != std::string::npos )
					{
						scheme = uri.raw.substr(0, pos);
						uri.location = uri.raw.substr(pos+1);
					}
				}
				else
				{
					pos = scheme.find_first_of(":#");
					if( pos != std::string::npos )
					{
						scheme = scheme.substr(0, pos);
					}

					uri.location = uri.raw;
				}

				if( scheme.empty() )
				{
					theVFS->errorLocation(AVM_OS_WARN)
							<< "Expected an uri like:> "
							<< "std:stream | file:path | socket:host:port !!!"
							<< std::endl;

					destroyLastUri();

					isConfigOK = false;

					continue;
				}

				if( (*itWfO)->getSpecifierOp() == AVM_OPCODE_PLUS )
				{
					uri.mode |= std::fstream::app;
				}

				if( scheme.starts_with("stream") )
				{
					if( not configureStream(theVFS, uri) )
					{
						destroyLastUri();

						isConfigOK = false;
					}
				}

				else if( scheme.starts_with("folder") )
				{
					if( not configureFolder(theVFS, uri) )
					{
						destroyLastUri();

						isConfigOK = false;
					}
				}

				else if( scheme.starts_with("filename") )
				{
					if( not configureFilename(theVFS, uri) )
					{
						destroyLastUri();

						isConfigOK = false;
					}
				}

				else if( scheme.starts_with("file") )
				{
					if( not configureFile(theVFS, uri) )
					{
						destroyLastUri();

						isConfigOK = false;
					}
				}

				else if( scheme.starts_with("socket") )
				{
					if( not configureSocket(theVFS, uri) )
					{
						destroyLastUri();

						isConfigOK = false;
					}
				}

				else
				{
					theVFS->errorLocation(AVM_OS_WARN)
							<< "Expected an uri like:> "
							<< "std:stream | file:path | socket:host:port !!!"
							<< std::endl;

					destroyLastUri();

					isConfigOK = false;
				}
			}
		}


		////////////////////////////////////////////////////////////////////////
		// The report PERIOD Attribute
		////////////////////////////////////////////////////////////////////////
		std::string strPeriod = Query::getWPropertyString(theVFS, "when", "");
		if( not strPeriod.empty() )
		{
			isConfigOK = configurePeriod(theVFS, strPeriod)
						&& isConfigOK;
		}


		if( mReportDetailsFlag )
		{
			SerializerFeature::toStream(AVM_OS_COUT);
		}
	}
	else
	{
//		theVFS->errorLocation(AVM_OS_WARN)
//				<< "Expected a REPORT section !!!" << std::endl;
	}

	return( true );
}


bool SerializerFeature::configureStream(const WObject * theVFS, AvmUri & uri)
{
	if( uri.location.find("std:") == 0 )
	{
		if( uri.location == "std:cout" )
		{
			uri.kind |= AVM_URI_STREAM_STD_COUT_KIND;
			uri.outStream.OS = AVM_OS_COUT.OS;
		}
		else if( uri.location == "std:cerr" )
		{
			uri.kind |= AVM_URI_STREAM_STD_CERR_KIND;
			uri.outStream.OS = AVM_OS_CERR.OS;
		}
		else
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "Expected an uri like:> "
					<< "std:( cout | cerr ) !!!" << std::endl;

			return false;
		}
	}

	else if( uri.location.find("avm:") == 0 )
	{
		if( uri.location == "avm:log" )
		{
			uri.kind |= AVM_URI_STREAM_AVM_LOG_KIND;
			uri.outStream.OS = AVM_OS_LOG.OS;
		}
		else if( uri.location == "avm:trace" )
		{
			uri.kind |= AVM_URI_STREAM_AVM_TRACE_KIND;
			uri.outStream.OS = AVM_OS_TRACE.OS;
		}
		else
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "Expected an uri like:> "
					<< "avm:( log | trace ) !!!" << std::endl;

			return false;
		}
	}

	return( true );
}


bool SerializerFeature::configureFolder(const WObject * theVFS, AvmUri & uri)
{
	uri.kind |= AVM_URI_FOLDER_KIND;

	if( uri.location == "avm:project" )
	{
		lastFolder.location = uri.location = VFS::ProjectPath;
	}
	else if( uri.location == "avm:output" )
	{
		lastFolder.location = uri.location = VFS::ProjectOutputPath;
	}
	else if( uri.location == "avm:source" )
	{
		lastFolder.location = uri.location = VFS::ProjectSourcePath;
	}
	else if( uri.location == "avm:log" )
	{
		lastFolder.location = uri.location = VFS::ProjectLogPath;
	}
	else
	{
		lastFolder.location = uri.location =
				VFS::native_path(uri.location, lastFolder.location);

		if ( not VFS::checkWritingFolder(uri.location) )
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "The folder `" << uri.location
					<< "' ---> doesn't exist or "
					"is not writable !!!" << std::endl;

			return( false );
		}
	}

	return( true );
}


bool SerializerFeature::configureFile(const WObject * theVFS, AvmUri & uri)
{
	uri.kind |= AVM_URI_FILE_KIND;

	uri.location = VFS::native_path(uri.location, lastFolder.location);

	if( mAutoOpenFileFlag )
	{
		uri.outStream = new std::ofstream(uri.location.c_str(), uri.mode);

		if( uri.outStream.good() )
		{
			uri.isAllocated = true;

			lastFile.location = uri.location;

			return( true );
		}
		else
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "Failed to open < " << uri.location
					<< " > file in write mode !!!" << std::endl;

			return( false );
		}
	}

	return( true );
}


bool SerializerFeature::configureFilename(const WObject * theVFS, AvmUri & uri)
{
	uri.kind |= AVM_URI_FILENAME_KIND;

	uri.location = VFS::native_path(uri.location, lastFolder.location);

	uri.outStream = new std::ofstream(uri.location.c_str(), uri.mode);

	if( uri.outStream.good() )
	{
		uri.isAllocated = true;

		lastFilename.location = uri.location;

		return( true );
	}
	else
	{
		theVFS->errorLocation(AVM_OS_WARN)
				<< "Failed to open < " << uri.location
				<< " > filename in write mode !!!" << std::endl;

		return( false );
	}
}


bool SerializerFeature::configureSocket(const WObject * theVFS, AvmUri & uri)
{
	uri.kind |= AVM_URI_SOCKET_KIND;

	std::string::size_type pos = uri.location.find(':');

	if( pos != std::string::npos )
	{
		if( not sep::from_string<std::uint64_t>(
				uri.location.substr(pos+1), uri.port, std::dec) )
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "Expected an uri<socket> with valid port number like:> "
					<< "socket:host:port !!!" << std::endl;

			return false;
		}

		uri.location = uri.location.substr(0, pos);
	}
	else
	{
		theVFS->errorLocation(AVM_OS_WARN)
				<< "Expected an uri like:> "
				<< "socket:host:port !!!" << std::endl;

		return false;
	}

	return( true );
}


bool SerializerFeature::configurePeriod(
		const WObject * theVFS, const std::string & strPeriod)
{
	std::string period;
	std::string::size_type pos;

	typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
	boost::char_separator<char> sep(":");

	tokenizer tokens(strPeriod, sep);
	tokenizer::iterator endIt = tokens.end();
	for( tokenizer::iterator it = tokens.begin() ; it != endIt ; ++it )
	{
		period = *it;

		if( period == "init" )
		{
			mPeriodKind |= AVM_PERIOD_INIT_KIND;
		}
		else if( period == "exit" )
		{
			mPeriodKind |= AVM_PERIOD_EXIT_KIND;
		}

		else if( period == "preprocess" )
		{
			mPeriodKind |= AVM_PERIOD_PREPROCESS_KIND;
		}
		else if( period == "postprocess" )
		{
			mPeriodKind |= AVM_PERIOD_POSTPROCESS_KIND;
		}

		else if( period == "prefilter" )
		{
			mPeriodKind |= AVM_PERIOD_PREFILTER_KIND;
		}
		else if( period == "postfilter" )
		{
			mPeriodKind |= AVM_PERIOD_POSTFILTER_KIND;
		}

		else if( period == "otf" )
		{
			mPeriodKind |= AVM_PERIOD_OTF_KIND;
		}
		else if( period.find("every") == 0  )
		{
			mPeriodKind |= AVM_PERIOD_EVERY_KIND;

			pos = period.find('?');
			if( (pos != std::string::npos) &&
				(not scanPeriod(period.substr(pos+1),
						mPeriodEveryValue, mPeriodEveryUnit)) )
			{
				theVFS->errorLocation(AVM_OS_WARN)
						<< "Expected a period like:> "
						<< "every?delay#unit !!!" << std::endl;

				return false;
			}
		}

		else if( period.find("after") == 0 )
		{
			mPeriodKind |= AVM_PERIOD_AFTER_KIND;

			pos = period.find('?');
			if( (pos != std::string::npos) &&
				(not scanPeriod(period.substr(pos+1),
						mPeriodAfterValue, mPeriodAfterUnit)) )
			{
				theVFS->errorLocation(AVM_OS_WARN)
						<< "Expected a period like:> "
						<< "after?delay#unit !!!" << std::endl;

				return false;
			}
		}

		else if( period.find("before") == 0 )
		{
			mPeriodKind |= AVM_PERIOD_BEFORE_KIND;

			pos = period.find('?');
			if( (pos != std::string::npos) &&
				(not scanPeriod(period.substr(pos+1),
						mPeriodBeforeValue, mPeriodBeforeUnit)) )
			{
				theVFS->errorLocation(AVM_OS_WARN)
						<< "Expected a period like:> "
						<< "before?delay#unit !!!" << std::endl;

				return false;
			}
		}

		else
		{
			theVFS->errorLocation(AVM_OS_WARN)
					<< "Expected a period like:> "
					<< "[ init ][:][ otf | (every | after | before)?"
							"value#unit][:][ exit ] !!!" << std::endl;

			return false;
		}
	}

	return( true );
}


/**
 * GETTER
 * Generate new outStream for a given index
 */
OutStream & SerializerFeature::newFileStream(std::size_t index)
{
	newIndexFile.close();

	if( not lastFilename.location.empty() )
	{
		newIndexFile.location = lastFilename.location;
	}
	else if( not lastFile.location.empty() )
	{
		newIndexFile.location = lastFile.location;
	}

	newIndexFile.location = (OSS() << VFS::stem( newIndexFile.location )
			<< "_" << index << VFS::extension( newIndexFile.location ));

	newIndexFile.location =
			VFS::native_path(newIndexFile.location, lastFolder.location);

	newIndexFile.outStream =
			new std::ofstream(newIndexFile.location.c_str(), newIndexFile.mode);

	if( newIndexFile.outStream.good() )
	{
		newIndexFile.isAllocated = true;

		return( newIndexFile.outStream );
	}
	else
	{
		AVM_OS_WARN << "Failed to open < " << newIndexFile.location
				<< " > file in write mode !!!" << std::endl;
	}

	return( AVM_OS_COUT );
}


OutStream & SerializerFeature::newFileStream(const std::string & filename)
{
	newIndexFile.close();

	if( not filename.empty() )
	{
		newIndexFile.location = filename;
	}
	else if( not lastFilename.location.empty() )
	{
		newIndexFile.location = lastFilename.location;
	}
	else if( not lastFile.location.empty() )
	{
		newIndexFile.location = lastFile.location;
	}
	else
	{
		newIndexFile.location = "newfile.txt";
	}

	newIndexFile.location =
			VFS::native_path(newIndexFile.location, lastFolder.location);

	newIndexFile.outStream =
			new std::ofstream(newIndexFile.location.c_str(), newIndexFile.mode);

	if( newIndexFile.outStream.good() )
	{
		newIndexFile.isAllocated = true;

		return( newIndexFile.outStream );
	}
	else
	{
		AVM_OS_WARN << "Failed to open < " << newIndexFile.location
				<< " > file in write mode !!!" << std::endl;
	}

	return( AVM_OS_COUT );
}

/**
 *******************************************************************************
 * SERIALIZATION
 *******************************************************************************
 */

std::string SerializerFeature::strPeriodKind(avm_period_kind_t kind)
{
	switch ( kind )
	{
		case AVM_PERIOD_INIT_KIND      : return( "init");
		case AVM_PERIOD_EXIT_KIND      : return( "exit");

		case AVM_PERIOD_OTF_KIND       : return( "otf");

		case AVM_PERIOD_EVERY_KIND     : return( "every");
		case AVM_PERIOD_AFTER_KIND     : return( "after");
		case AVM_PERIOD_BEFORE_KIND    : return( "before");

		case AVM_PERIOD_UNDEFINED_KIND : return( "undefined<period#kind>");

		default                        : return( "unknown<period#kind>" );
	}
}


void SerializerFeature::toStream(OutStream & os) const
{
	os << TAB << "report:" << EOL;

	os << TAB2 << "details = "
			<< (mReportDetailsFlag ? "true" : "false") << ";"
			<< EOL_INCR_INDENT;

	for( auto & anUri : mTableOfURI )
	{
		anUri.toStream(os);
	}

	std::string sep = "";
	os << DECR_INDENT_TAB2 << "when = ";

	if( IS_PERIOD_INIT_KIND(mPeriodKind) )
	{
		os << "init";
		sep = ":";
	}

	if( IS_PERIOD_AFTER_KIND(mPeriodKind) )
	{
		os << (sep = ":") << "after?" << mPeriodAfterValue
				<< "#" << strUnit(mPeriodAfterUnit);
		;
	}

	if( IS_PERIOD_OTF_KIND(mPeriodKind) )
	{
		os << (sep = ":") << "otf";
	}

	if( IS_PERIOD_EVERY_KIND(mPeriodKind) )
	{
		os << (sep = ":") << "every?" << mPeriodEveryValue
				<< "#" << strUnit(mPeriodEveryUnit);
	}

	if( IS_PERIOD_BEFORE_KIND(mPeriodKind) )
	{
		os << (sep = ":") << "before?" << mPeriodBeforeValue
				<< "#" << strUnit(mPeriodBeforeUnit);
	}

	if( IS_PERIOD_EXIT_KIND(mPeriodKind) )
	{
		os << (sep = ":") << "exit";
	}
	os << ";" << EOL;
}


} /* namespace sep */
