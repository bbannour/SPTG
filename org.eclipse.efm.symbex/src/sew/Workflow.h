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

#ifndef WORKFLOW_WORKFLOW_H_
#define WORKFLOW_WORKFLOW_H_

#include <common/AvmPointer.h>
#include <common/RunnableElement.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <util/avm_vfs.h>


namespace sep
{

class SymbexEngine;


class Workflow  :  public RunnableElement
{

	AVM_DECLARE_UNCLONABLE_CLASS(Workflow)

public:
	/**
	* GLOBALS
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

	// Symbex Threading config
	bool mMultitaskingFlag;
	avm_uint8_t mThreadCount;

	// Shell config
	std::string mInconditionalStopMarkerLocation;

	// TDD config
	bool mTddRegressionTestingFlag;
	bool mTddUnitTestingFlag;

	SymbexEngine * mMainSymbexEngine;
	SymbexEngine * mCurrentSymbexEngine;


public:
	/**
	 * SINGLETON
	 */
	static Workflow * INSTANCE;


	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Workflow(const std::string & sewBuildID)
	: RunnableElement( NULL ),
	mSEWBuildID( sewBuildID ),
	mSEWFileLocation( ),
	mWObjectManager( WObject::SEW_FQN_ROOT ),

	// Symbex Threading config
	mMultitaskingFlag( false ),
	mThreadCount( 1 ),

	// Shell config
	mInconditionalStopMarkerLocation( ),

	mTddRegressionTestingFlag( false ),
	mTddUnitTestingFlag( false ),

	mMainSymbexEngine( NULL ),
	mCurrentSymbexEngine( NULL )
	{
		INSTANCE = this;
	}

	/**
	 * DESTRUCTOR
	 */
	virtual ~Workflow()
	{
		//!! NOTHING
	}


	/**
	 * LOADER - DISPOSER
	 */
	bool load();

	void dispose();

	/**
	 * GETTER
	 * mWObjectManager
	 */
	inline  WObjectManager & getWObjectManager()
	{
		return( mWObjectManager );
	}


	/**
	 * Symbex Threading config
	 */
	inline bool isMultitasking() const
	{
		return( mMultitaskingFlag );
	}

	inline avm_uint8_t getThreadCount() const
	{
		return( mThreadCount );
	}

	/**
	 * GETTER
	 * mInconditionalStopMarkerLocation
	 */
	inline const std::string & getInconditionalStopMarkerLocation() const
	{
		return( mInconditionalStopMarkerLocation );
	}


	////////////////////////////////////////////////////////////////////////////
	// CONFIGURE API
	////////////////////////////////////////////////////////////////////////////
	bool loadConfiguration(const std::string & aWorkflowLocation);

	bool parseConfiguration();

	bool loadCoreElementsConfig(OutStream & LOGGER);

	bool loadWorkspaceLocationsConfig(OutStream & LOGGER);

	bool loadSymbexConfig();

	bool loadShellConfig();

	bool loadTddConfig();

	bool loadOthersConfig();

	virtual bool configure();


	/**
	 * Prologue options
	 */
	void setPrologueOption(const std::string & id, BF value);


	////////////////////////////////////////////////////////////////////////////
	// START / STOP / KILL / SUSPEND / RESUME  API
	////////////////////////////////////////////////////////////////////////////

	virtual bool start();


	////////////////////////////////////////////////////////////////////////////
	// INIT / EXIT API
	////////////////////////////////////////////////////////////////////////////

	inline virtual bool initImpl()
	{
		return( true );
	}

	virtual bool exitImpl();



	/**
	 * REPORT TRACE
	 */
	virtual void report(OutStream & os) const;


	/*
	 * PROCESSING
	 */
	bool startComputing();


	/**
	 * STANDARD SEQUENCE
	 */
	inline WObject * getCONSOLE() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_CONSOLE_REGEX_ID) );
	}

	inline WObject * getDEVELOPER() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_DEVELOPER_REGEX_ID) );
	}

	inline WObject * getDIRECTOR() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_DIRECTOR_REGEX_ID, mParameterWObject) );
	}

	inline WObject * getSHELL() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_SHELL_REGEX_ID) );
	}

	inline WObject * getSYMBEX() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_SYMBEX_REGEX_ID) );
	}

	inline WObject * getTDD() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_TDD_REGEX_ID) );
	}

	inline WObject * getWORKSPACE() const
	{
		return( Query::getRegexWSequence(mParameterWObject,
				Workflow::SECTION_WORKSPACE_REGEX_ID) );
	}


	/**
	 ***************************************************************************
	// TEST DRIVEN DEVELOPMENT
	section TDD
		report = "reportName";

		regression = true;
		unit = true;
	endsection TDD
	 ***************************************************************************
	 */
	inline bool hasTddReport()
	{
		return( Query::hasWPropertyString(getTDD(), "report") );
	}

	inline std::string getTddReport(const std::string & aDefaultValue = "report.tdd")
	{
		std::string aLocation =
				Query::getWPropertyString(getTDD(), "report", aDefaultValue);

		std::string::size_type pos = aLocation.find_last_of('.');
		if( pos != std::string::npos )
		{
			aLocation.insert(pos, "_avm_" + mSEWBuildID);
		}
		else
		{
			aLocation = aLocation + "_avm_" + mSEWBuildID + ".tdd";
		}

		return( VFS::native_path(aLocation) );
	}

	inline std::string getTddReportLocation(
			const std::string & aDefaultValue = "report.tdd")
	{
		return( VFS::native_path(
				getTddReport(aDefaultValue), VFS::WorkspaceTddPath) );
	}

	inline bool isTddRegressionTesting(bool aDefaultValue = false)
	{
		return( mTddRegressionTestingFlag );
	}

	inline bool isTddUnitTesting(bool aDefaultValue = false)
	{
		return( mTddUnitTestingFlag );
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
	inline bool needDeveloperDebugLogTraceFolder()
	{
		return( hasDeveloperDebugLogFile()
				|| hasDeveloperDebugTraceFile() );
	}

	inline bool hasDeveloperDebugLogFile()
	{
		return( Query::hasWPropertyString(getDEVELOPER(), "log") );
	}

	inline std::string getDeveloperDebugLogFile(
			const std::string & aDefaultValue = "avm.log")
	{
		return( VFS::native_path( Query::getWPropertyString(
				getDEVELOPER(), "log", aDefaultValue) ) );
	}

	inline std::string getDeveloperDebugLogFileLocation(
			const std::string & aDefaultValue = "avm.log")
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

	inline bool hasDeveloperDebugTraceFile()
	{
		return( Query::hasWPropertyString(getDEVELOPER(), "debug") );
	}

	inline std::string getDeveloperDebugTraceFile(
			const std::string & aDefaultValue = "avm.dbg")
	{
		return( VFS::native_path( Query::getWPropertyString(
				getDEVELOPER(), "debug", aDefaultValue)) );
	}

	inline std::string getDeveloperDebugTraceFileLocation(
			const std::string & aDefaultValue = "avm.dbg")
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

#endif /* WORKFLOW_WORKFLOW_H_ */
