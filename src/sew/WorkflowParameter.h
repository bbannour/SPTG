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

#ifndef WORKFLOW_WORKFLOW_PARAMETER_H_
#define WORKFLOW_WORKFLOW_PARAMETER_H_


#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <util/avm_vfs.h>
#include <util/avm_numeric.h>

namespace sep
{

class WorkflowParameter final
{

public:
	/**
	* GLOBALS
	* WORKFLOW SECTION NAME
	*/
	static const std::string & SECTION_WORKSPACE_REGEX_ID;

	static const std::string & SECTION_CONSOLE_REGEX_ID;

	static const std::string & SECTION_DEVELOPER_REGEX_ID;

	static const std::string & SECTION_DIRECTOR_REGEX_ID;

	static const std::string & SECTION_SHELL_REGEX_ID;

	static const std::string & SECTION_SYMBEX_REGEX_ID;

	static const std::string & SECTION_TDD_REGEX_ID;

	static const std::string & SECTION_FAM_REGEX_ID;

	static const std::string & SECTION_FAM_CONTAINERS_REGEX_ID;

	// Deprecated
	static const std::string & SECTION_FAM_QUEUE_REGEX_ID;

	static const std::string & SECTION_FAM_REDUNDANCY_REGEX_ID;

	static const std::string & SECTION_FAM_PROCESSOR_REGEX_ID;

	static const std::string & SECTION_FAM_FILTER_REGEX_ID;

	static const std::string & SECTION_FAM_PREPROCESS_REGEX_ID;

	static const std::string & SECTION_FAM_POSTPROCESS_REGEX_ID;


protected:
	/**
	* ATTRIBUTES
	*/
	const std::string mSEWBuildID;

	std::string mSEWFileLocation;

	WObjectManager mWObjectManager;

	const WObject * mParameterWObject;

public:
	/**
	 * SINGLETON
	 */
	static WorkflowParameter * INSTANCE;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	WorkflowParameter(const std::string & sewBuildID)
	: mSEWBuildID( sewBuildID ),
	mSEWFileLocation( ),
	mWObjectManager( WObject::SEW_FQN_ROOT ),

	mParameterWObject( nullptr )
	{
		INSTANCE = this;
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~WorkflowParameter()
	{
		//!! NOTHING
	}


	/**
	 * GETTER
	 * mWObjectManager
	 */
	inline  WObjectManager & getWObjectManager()
	{
		return( mWObjectManager );
	}

	/**
	 * GETTER
	 * mParameterWObject
	 */
	inline const WObject * getParameterWObject() const
	{
		return( mParameterWObject );
	}

	inline bool hasParameterWObject() const
	{
		return( mParameterWObject != WObject::_NULL_ );
	}

	void setParameterWObject(const WObject * wfParameterObject)
	{
		mParameterWObject = wfParameterObject;
	}

	const WObject * getEngineWObject() const;


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////
	bool loadConfiguration(const std::string & aWorkflowLocation);

	bool loadConfiguration(const std::string & rawWorkflow,
			const std::string & aWorkflowLocation);

	bool loadConfiguration(std::istream & anInputStream);

	bool parseConfiguration(std::istream & anInputStream);

	bool loadCoreElementsConfig(OutStream & LOGGER);

	bool loadWorkspaceLocationsConfig(OutStream & LOGGER);


	/**
	 * Prologue options
	 */
	void setPrologueOption(const std::string & id, BF value);


	/**
	 * STANDARD SEQUENCE
	 */
	inline const WObject * getDEVELOPER() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				WorkflowParameter::SECTION_DEVELOPER_REGEX_ID) );
	}

	inline const WObject * getDIRECTOR() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				WorkflowParameter::SECTION_DIRECTOR_REGEX_ID, mParameterWObject) );
	}


	/**
	 ***************************************************************************
	section TRACE --> developer
		log = "avm.log";

		debug = "avm.trace";
		level = 'MEDIUM'; // ZERO < LOW < MEDIUM < HIGH < ULTRA

		kind = 'PARSING'; --> flag = 'PARSING';
		kind = 'COMPILING';
		kind = 'COMPUTING';

		kind = 'TRACE';

		kind = 'PROCESSOR';

		kind = 'PROGRAM';
		kind = 'STATEMENT';
		kind = 'BYTECODE';

		kind = 'STMNT_ASSIGN';

	endsection TRACE --> developer
	 ***************************************************************************
	 */
	inline bool needDeveloperDebugLogTraceFolder() const
	{
		return( hasDeveloperDebugLogFile()
				|| hasDeveloperDebugTraceFile() );
	}

	inline bool hasDeveloperDebugLogFile() const
	{
		return( Query::hasWPropertyString(getDEVELOPER(), "log") );
	}

	inline std::string getDeveloperDebugLogFile(
			const std::string & aDefaultValue = "avm.log") const
	{
		return( VFS::native_path( Query::getWPropertyString(
				getDEVELOPER(), "log", aDefaultValue) ) );
	}

	inline std::string getDeveloperDebugLogFileLocation(
			const std::string & aDefaultValue = "avm.log") const
	{
		return( VFS::native_path(
				getDeveloperDebugLogFile(aDefaultValue),
				VFS::WorkspaceLogPath) );
	}

	/**
	 ***************************************************************************
	 * GLOBAL DEBUG LEVEL
	 *
	 * debug = "avm.trace";
	 * level = 'ZERO'; // ZERO < LOW < MEDIUM < HIGH < ULTRA
	 ***************************************************************************
	 */

	inline bool hasDeveloperDebugTraceFile() const
	{
		return( Query::hasWPropertyString(getDEVELOPER(), "debug") );
	}

	inline std::string getDeveloperDebugTraceFile(
			const std::string & aDefaultValue = "avm.dbg") const
	{
		return( VFS::native_path( Query::getWPropertyString(
				getDEVELOPER(), "debug", aDefaultValue)) );
	}

	inline std::string getDeveloperDebugTraceFileLocation(
			const std::string & aDefaultValue = "avm.dbg") const
	{
		return( VFS::native_path(
				getDeveloperDebugTraceFile(aDefaultValue),
				VFS::WorkspaceLogPath) );
	}


	/**
	 ***************************************************************************
	 * SERIALIZATION
	 ***************************************************************************
	 */
	void toStream(OutStream & os) const;

};

} /* namespace sep */

#endif /* WORKFLOW_WORKFLOW_PARAMETER_H_ */
