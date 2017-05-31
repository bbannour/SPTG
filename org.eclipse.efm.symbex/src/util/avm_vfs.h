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

#ifndef AVM_VFS_H_
#define AVM_VFS_H_

#include <string>
#include <vector>


namespace sep
{

struct VFS
{
	/**
	 * ATTRIBUTE
	 */
	static std::string ExecutablePath;

	static std::string WorkflowPath;


	static std::string LaunchPath;


	static std::string WorkspaceRootPath;

	static std::string WorkspaceSourcePath;

	static std::string WorkspaceOutputPath;

	static std::string WorkspaceLogPath;

	static std::string WorkspaceDebugPath;

	static std::string WorkspaceTddPath;


	static std::string ProjectPath;

	static std::string ProjectSourcePath;

	static std::string ProjectOutputPath;

	static std::string ProjectLogPath;

	static std::string ProjectDebugPath;

	static std::string ProjectTddPath;


	/**
	 * FORMAT NATIVE FILE / DIRECTORY PATH
	 */
	static std::string native_path(const std::string & path);
	static std::string native_path(
			const std::string & path, const std::string & main_dir);

	static std::string posix_path(const std::string & path);


	/**
	 * CHECKER FOR READING / WRITING  FILE / DIRECTORY PATH
	 */
	static bool checkReadingFile(const std::string & path);
	static bool checkWritingFile(const std::string & path);

	static bool checkWritingFileFolder(const std::string & path);

	static bool checkReadingFolder(const std::string & dir_path);
	static bool checkWritingFolder(const std::string & dir_path);


	/**
	 * List all files
	 */
	static bool listAllFiles(
			const std::string & dir_path,
			std::vector< std::string > & listOfFiles,
			bool recursive = false);

	/**
	 * copy / move
	 */
	static bool copyTo(
			const std::string & srcLocation,
			const std::string & destLocation);

	static bool copyToFolder(
			const std::string & srcLocation,
			const std::string & destLocation);


	static bool moveTo(
			const std::string & srcLocation,
			const std::string & destLocation);

	static bool moveToFolder(
			const std::string & srcLocation,
			const std::string & destLocation);


	/**
	 * UTILS
	 */
	static const char PathSeparator;

	static bool isPathSeparator(char c);


	static std::string parent(const std::string & aLocation);

	static std::string filename(const std::string & aLocation);

	static std::string stem(const std::string & aLocation);

	inline static std::string basename(const std::string & aLocation)
	{
		return( stem(aLocation ) );
	}

	static std::string extension(const std::string & aLocation);

	static std::string replace_extension(
			const std::string & aLocation,
			const std::string & newExtension);


	static std::string prefixFilename(
			const std::string & aLocation,
			const std::string & aPrefix,
			const std::string & newExtension = "");

	static std::string suffixFilename(
			const std::string & aLocation,
			const std::string & aPrefix,
			const std::string & newExtension = "");

	static std::string relativePath(
			const std::string & refPath,
			const std::string & aPath,
			const std::string & newPrefix = "");

	inline static std::string relativeWorkspacePath(
			const std::string & aPath,
			const std::string & newPrefix = "<wroot>:")
	{
		return( relativePath(WorkspaceRootPath, aPath, newPrefix) );
	}

	inline static std::string relativeProjectPath(
			const std::string & aPath,
			const std::string & newPrefix = "<proj>:")
	{
		return( relativePath(ProjectPath, aPath, newPrefix) );
	}

	inline static std::string relativeProjectSourcePath(
			const std::string & aPath,
			const std::string & newPrefix = "<src>:")
	{
		return( relativePath(ProjectSourcePath, aPath, newPrefix) );
	}

	inline static std::string relativeProjectOutputPath(
			const std::string & aPath,
			const std::string & newPrefix = "<out>:")
	{
		return( relativePath(ProjectOutputPath, aPath, newPrefix) );
	}

	inline static std::string relativeLogPath(
			const std::string & aPath,
			const std::string & newPrefix = "<log>:")
	{
		return( relativePath(ProjectLogPath, aPath, newPrefix) );
	}

	inline static std::string relativeProjectTddPath(
			const std::string & aPath,
			const std::string & newPrefix = "<tdd>:")
	{
		return( relativePath(ProjectTddPath, aPath, newPrefix) );
	}


	static std::string wrapPath(const std::string & aPath,
			std::size_t wrapSize, const std::string & newPrefix = "..." );

};

} /* namespace sep */

#endif /* AVM_VFS_H_ */
