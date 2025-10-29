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

#include <printer/OutStream.h>

#include <filesystem>
#include <fstream>
#include <vector>

//#include <boost/filesystem.hpp>


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

//static bool is_absolute(const std::filesystem::path & aPath)
//{
////	return( aPath.is_absolute() );
//
//	if( aPath.is_absolute() )
//	{
//		return( true );
//	}
//	else
//	{
//#ifdef __AVM_BOOST_WINDOWS__
//		std::string root = aPath.root_path().generic_string();
//		return( (root.size() >= 2) &&
//				((root[root.size()-1] == ':')
//				|| (root.find(':') != std::string::npos)   // "c:"
//				|| ((root[0] == '/') && (root[1] == '/'))  // "//share"
//				|| aPath.is_absolute()
//				)
//		);
//#else
//		return( aPath.is_absolute() );
//#endif
//	}
////	else if( VFS::IS_WINDOWS_PLATFORM && (! aPath.empty()) )
////	{
////		std::string root = aPath.root_path().generic_string();
////		return( (root.size() == 2) && (root[1] == ':') );
////	}
//
//	return( false );
//}


std::string VFS::native_path(const std::string & path)
{
	std::filesystem::path aPath( path );

//	if( aPath.is_relative() )
//	{
//		aPath = std::filesystem::current_path().generic_string() +
//				"/" + aPath.generic_string();
//	}
	aPath = std::filesystem::weakly_canonical(aPath);

	return( aPath.generic_string() );
}

std::string VFS::native_path(
		const std::string & path, const std::string & main_dir)
{
	std::filesystem::path aPath( path );

//	if( not aPath.is_absolute() )
	if( aPath.is_relative() )
	{
		aPath = main_dir + "/" + aPath.generic_string();
		aPath = std::filesystem::weakly_canonical(aPath);
	}

	return( aPath.generic_string() );
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
		std::filesystem::path aPath( path );

		return( std::filesystem::exists(aPath) /*&&
				std::filesystem::is_regular_file(aPath)*/ );
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
		std::filesystem::path aPath( dir_path );

		return( std::filesystem::exists(aPath) &&
				std::filesystem::is_directory(aPath) );
	}
	catch( const std::exception & e )
	{
		AVM_OS_CERR << std::endl
				<< EMPHASIS("std::exception:>", e.what(), '*', 80);
	}

	return( false );
}

bool VFS::checkWritingFolder(const std::string & dir_path, bool cleaningRequired)
{
	try
	{
		std::filesystem::path aPath( dir_path );

		if( cleaningRequired
			&& std::filesystem::exists(aPath)
			&& std::filesystem::is_directory(aPath)
			&& (not std::filesystem::is_empty(aPath)) )
		{
			std::filesystem::remove_all(aPath);
		}

		std::filesystem::create_directories( aPath );

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
		std::filesystem::path aPath( dir_path );

		std::filesystem::directory_iterator end_itr;
		std::filesystem::directory_iterator itr(aPath);

		for( ; itr != end_itr ; ++itr )
		{
			// If it's not a directory, list it.
			// If you want to list directories too, just remove this check.
			if( std::filesystem::is_regular_file( itr->status() ) )
			{
				if( VFS::checkReadingFile( itr->path().generic_string() ) )
				{
					listOfFiles.push_back( itr->path().generic_string() );
				}
			}
			else if( recursive &&
					std::filesystem::is_directory( itr->status() ) )
			{
				if( VFS::listAllFiles(itr->path().generic_string(), listOfFiles, true) )
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
		std::filesystem::copy_file(srcLocation, destLocation,
				std::filesystem::copy_options::overwrite_existing);

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
		std::filesystem::path srcPath( srcLocation );
		std::filesystem::path destPath( destLocation );

		destPath /= srcPath.filename();

		std::filesystem::copy_file(srcPath, destPath,
				std::filesystem::copy_options::overwrite_existing);

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
			return( std::filesystem::remove( srcLocation ) );
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
			return( std::filesystem::remove( srcLocation ) );
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
		std::filesystem::path::preferred_separator;


bool VFS::isPathSeparator(char c)
{
	return( (c == std::filesystem::path::preferred_separator) ||
			(c == ('/')) || (c == ('\\')) );
}


std::string VFS::parent(const std::string & aLocation)
{
	std::filesystem::path aPath( aLocation );

	return( aPath.parent_path().generic_string() );
}

std::string VFS::filename(const std::string & aLocation)
{
	std::filesystem::path aPath( aLocation );

	return( aPath.filename().generic_string() );
}

std::string VFS::stem(const std::string & aLocation)
{
	std::filesystem::path aPath( aLocation );

	return( aPath.stem().generic_string() );
}

std::string VFS::extension(const std::string & aLocation)
{
	std::filesystem::path aPath( aLocation );

	return( aPath.extension().generic_string() );
}

std::string VFS::replace_extension(
		const std::string & aLocation, const std::string & anExtension)
{
	std::filesystem::path aPath( aLocation );

	std::filesystem::path newPath = aPath.replace_extension(anExtension);

	return( newPath.generic_string() );
}


std::string VFS::prefixFilename(const std::string & aLocation,
		const std::string & aPrefix, const std::string & newExtension)
{
	std::filesystem::path aPath( aLocation );

	std::filesystem::path newPath = aPath.parent_path();

	newPath /= aPrefix + aPath.filename().generic_string();

	if( newExtension.size() > 1 )
	{
		newPath = newPath.replace_extension(newExtension);
	}

	return( newPath.generic_string() );
}

std::string VFS::suffixFilename(const std::string & aLocation,
		const std::string & aPrefix, const std::string & newExtension)
{
	std::filesystem::path aPath( aLocation );

	std::filesystem::path newPath = aPath.parent_path();
	newPath /= aPath.stem().generic_string() + aPrefix +
			( (newExtension.size() > 1) ?
					newExtension : aPath.extension().generic_string() );

	return( newPath.generic_string() );
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
