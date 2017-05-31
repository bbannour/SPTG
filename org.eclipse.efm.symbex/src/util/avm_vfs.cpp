/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 26 mars 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "avm_vfs.h"

#include <collection/Typedef.h>

#include <fstream>

#include <boost/filesystem.hpp>


namespace sep
{

std::string VFS::ExecutablePath;

std::string VFS::WorkflowPath;


std::string VFS::LaunchPath;


std::string VFS::WorkspaceRootPath;

std::string VFS::WorkspaceSourcePath;

std::string VFS::WorkspaceOutputPath;

std::string VFS::WorkspaceLogPath;

std::string VFS::WorkspaceDebugPath;

std::string VFS::WorkspaceTddPath;


std::string VFS::ProjectPath;

std::string VFS::ProjectSourcePath;

std::string VFS::ProjectOutputPath;

std::string VFS::ProjectLogPath;

std::string VFS::ProjectDebugPath;

std::string VFS::ProjectTddPath;




/**
 * FORMAT NATIVE FILE / DIRECTORY PATH
 */

static bool is_complete(const boost::filesystem::path & aPath)
{
//	return( aPath.is_absolute() );

	if( aPath.is_complete() )
	{
		return( true );
	}
	else
	{
#ifdef __AVM_BOOST_WINDOWS__
		std::string root = aPath.root_path().string();
		return( (root.size() >= 2) &&
				((root[root.size()-1] == ':')
				|| (root.find(':') != std::string::npos)   // "c:"
				|| ((root[0] == '/') && (root[1] == '/'))  // "//share"
				|| aPath.is_complete()
				)
		);
#else
		return( aPath.is_complete() );
#endif
	}
//	else if( VFS::IS_WINDOWS_PLATFORM && (! aPath.empty()) )
//	{
//		std::string root = aPath.root_path().string();
//		return( (root.size() == 2) && (root[1] == ':') );
//	}

	return( false );
}


std::string VFS::native_path(const std::string & path)
{
	boost::filesystem::path aPath( path );

//	if( not is_complete(aPath) )
//	{
//		aPath = boost::filesystem::current_path().string() +
//				"/" + aPath.string();
//	}
	aPath.normalize();

	return( aPath.string() );
}

std::string VFS::native_path(
		const std::string & path, const std::string & main_dir)
{
	boost::filesystem::path aPath( path );

	if( not is_complete(aPath) )
//	if( aPath.is_relative() )
	{
		aPath = main_dir + "/" + aPath.string();
		aPath.normalize();
	}

	return( aPath.string() );
}

// CYGWIN
std::string VFS::posix_path(const std::string & path)
{
//	if( VFS::IS_CYGWYN_PLATFORM )
#ifdef __AVM_BOOST_CYGWIN__
	if( (path.size() > 2) && (path[1] == ':') )
	{
		path[0] = tolower(path[0]);
		path[1] = '/';
		if( (path[2] == '/') || (path[2] == '\\') )
		{
			path = "/cygdrive/" + path.substr(0, 2) + path.substr(3) ;
		}
		else
		{
			path = "/cygdrive/" + path;
		}
	}
#endif

	return( path );
}


/**
 * CHECKER FOR READING / WRITING  FILE / DIRECTORY PATH
 */
bool VFS::checkReadingFile(const std::string & path)
{
	try
	{
		boost::filesystem::path aPath( path );

		return( boost::filesystem::exists(aPath) /*&&
				boost::filesystem::is_regular_file(aPath)*/ );
	}
	catch( const std::exception & e )
	{
		AVM_OS_CERR << std::endl
				<< EMPHASIS("std::exception:>", e.what(), '*', 80);
	}

	return( false );
}

bool VFS::checkWritingFile(const std::string & path)
{
	std::ofstream checkFileStream(path.c_str());

	return( checkFileStream.good() );
}

bool VFS::checkWritingFileFolder(const std::string & path)
{
	std::string::size_type pos = path.find_last_of( VFS::PathSeparator );

	if( pos != std::string::npos )
	{
		if( not VFS::checkWritingFolder( path.substr(0, pos) ) )
		{
			return( false );
		}
	}

	return( VFS::checkWritingFile( path ) );
}


bool VFS::checkReadingFolder(const std::string & dir_path)
{
	try
	{
		boost::filesystem::path aPath( dir_path );

		return( boost::filesystem::exists(aPath) &&
				boost::filesystem::is_directory(aPath) );
	}
	catch( const std::exception & e )
	{
		AVM_OS_CERR << std::endl
				<< EMPHASIS("std::exception:>", e.what(), '*', 80);
	}

	return( false );
}

bool VFS::checkWritingFolder(const std::string & dir_path)
{
	try
	{
		boost::filesystem::path aPath( dir_path );

		boost::filesystem::create_directories( aPath );

		return( true );
	}
	catch( const std::exception & e )
	{
		AVM_OS_CERR << std::endl
				<< EMPHASIS("std::exception:>", e.what(), '*', 80);

		return( false );
	}

	return( false );
}


/**
 * List all file
 */
bool VFS::listAllFiles(const std::string & dir_path,
		std::vector< std::string > & listOfFiles, bool recursive)
{
	if( VFS::checkReadingFolder(dir_path) )
	{
		boost::filesystem::path aPath( dir_path );

		boost::filesystem::directory_iterator end_itr;
		boost::filesystem::directory_iterator itr(aPath);

		for( ; itr != end_itr ; ++itr )
		{
			// If it's not a directory, list it.
			// If you want to list directories too, just remove this check.
			if( boost::filesystem::is_regular_file( itr->status() ) )
			{
				if( VFS::checkReadingFile( itr->path().string() ) )
				{
					listOfFiles.push_back( itr->path().string() );
				}
			}
			else if( recursive &&
					boost::filesystem::is_directory( itr->status() ) )
			{
				if( VFS::listAllFiles(itr->path().string(), listOfFiles, true) )
				{
					//!! continue
				}
			}
		}

		return( true );
	}

	return( false );
}


/**
 * copy / move
 */
bool VFS::copyTo(
		const std::string & srcLocation,
		const std::string & destLocation)
{
	try
	{
		boost::filesystem::copy_file(srcLocation, destLocation,
				boost::filesystem::copy_option::overwrite_if_exists);

		return( true );
	}
	catch( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"VFS::copyToFolder< std::exception >", e.what(), '*', 80);
	}
	catch( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			"VFS::copyToFolder< unknown::exception > !!!", '*', 80 );
	}

	return( false );
}

bool VFS::copyToFolder(
		const std::string & srcLocation,
		const std::string & destLocation)
{
	try
	{
		boost::filesystem::path srcPath( srcLocation );
		boost::filesystem::path destPath( destLocation );

		destPath /= srcPath.filename();

		boost::filesystem::copy_file(srcPath, destPath,
				boost::filesystem::copy_option::overwrite_if_exists);

		return( true );
	}
	catch( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"VFS::copyToFolder< std::exception >", e.what(), '*', 80);
	}
	catch( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			"VFS::copyToFolder< unknown::exception > !!!", '*', 80);
	}

	return( false );
}


bool VFS::moveTo(
		const std::string & srcLocation,
		const std::string & destLocation)
{
	try
	{
		if( VFS::copyTo(srcLocation, destLocation) )
		{
			return( boost::filesystem::remove( srcLocation ) );
		}
	}
	catch( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"VFS::moveToFolder< std::exception >", e.what(), '*', 80);
	}
	catch( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			"VFS::moveToFolder< unknown::exception > !!!", '*', 80);
	}

	return( false );
}

bool VFS::moveToFolder(
		const std::string & srcLocation, const std::string & destLocation)
{
	try
	{
		if( VFS::copyToFolder(srcLocation, destLocation) )
		{
			return( boost::filesystem::remove( srcLocation ) );
		}
	}
	catch( const std::exception & e )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
				"VFS::moveToFolder< std::exception >", e.what(), '*', 80);
	}
	catch( ... )
	{
		AVM_OS_WARN << std::endl << EMPHASIS(
			"VFS::moveToFolder< unknown::exception > !!!", '*', 80);
	}

	return( false );
}


/**
 * UTILS
 */
const char VFS::PathSeparator =
		boost::filesystem::path::preferred_separator;


bool VFS::isPathSeparator(char c)
{
	return( (c == boost::filesystem::path::preferred_separator) ||
			(c == ('/')) || (c == ('\\')) );
}


std::string VFS::parent(const std::string & aLocation)
{
	boost::filesystem::path aPath( aLocation );

	return( aPath.parent_path().string() );
}

std::string VFS::filename(const std::string & aLocation)
{
	boost::filesystem::path aPath( aLocation );

	return( aPath.filename().string() );
}

std::string VFS::stem(const std::string & aLocation)
{
	boost::filesystem::path aPath( aLocation );

	return( aPath.stem().string() );
}

std::string VFS::extension(const std::string & aLocation)
{
	boost::filesystem::path aPath( aLocation );

	return( aPath.extension().string() );
}

std::string VFS::replace_extension(
		const std::string & aLocation, const std::string & anExtension)
{
	boost::filesystem::path aPath( aLocation );

	boost::filesystem::path newPath = aPath.replace_extension(anExtension);

	return( newPath.string() );
}


std::string VFS::prefixFilename(const std::string & aLocation,
		const std::string & aPrefix, const std::string & newExtension)
{
	boost::filesystem::path aPath( aLocation );

	boost::filesystem::path newPath = aPath.parent_path();

	newPath /= aPrefix + aPath.filename().string();

	if( newExtension.size() > 1 )
	{
		newPath = newPath.replace_extension(newExtension);
	}

	return( newPath.string() );
}

std::string VFS::suffixFilename(const std::string & aLocation,
		const std::string & aPrefix, const std::string & newExtension)
{
	boost::filesystem::path aPath( aLocation );

	boost::filesystem::path newPath = aPath.parent_path();
	newPath /= aPath.stem().string() + aPrefix +
			( (newExtension.size() > 1) ?
					newExtension : aPath.extension().string() );

	return( newPath.string() );
}


std::string VFS::relativePath(const std::string & refPath,
		const std::string & aPath, const std::string & newPrefix)
{
	if( refPath.size() < aPath.size() )
	{
		std::string::size_type pos = 0;

		for( ; pos < refPath.size() ; ++pos )
		{
			if( (refPath[pos] != aPath[pos]) &&
				(not isPathSeparator(refPath[pos])) &&
				(not isPathSeparator(aPath[pos])) )
			{
				break;
			}
		}

		if( pos > 0 )
		{
			if( newPrefix.empty() )
			{
				while( isPathSeparator(aPath[pos]) )
				{
					++pos;
				}

				return( aPath.substr(pos) );
			}

			return( newPrefix + aPath.substr(pos) );
		}
	}
	else if( refPath.size() == aPath.size() )
	{
		return( newPrefix + "./" );
	}

	return( aPath );
}



std::string VFS::wrapPath(const std::string & aPath,
		std::size_t wrapSize, const std::string & newPrefix)
{
	if( aPath.size() > wrapSize )
	{
		std::string::size_type posSeparator = 0;

		for( std::string::size_type pos = 0 ; pos < aPath.size() ; ++pos )
		{
			if( isPathSeparator(aPath[pos]) )
			{
				posSeparator = pos;
				if( wrapSize >= (aPath.size() - pos) )
				{
					break;
				}
			}
		}

		if( posSeparator > 0 )
		{
			return( newPrefix + aPath.substr(posSeparator) );
		}

		return( aPath );
	}

	return( aPath );
}


} /* namespace sep */
