/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 14 déc. 2016
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and Implementation
 ******************************************************************************/

#ifndef FML_WORKFLOW_CONFIGURATION_H_
#define FML_WORKFLOW_CONFIGURATION_H_

#include <common/NamedElement.h>

#include <fml/infrastructure/System.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/workflow/WObject.h>

#include <printer/OutStream.h>



namespace sep
{

class APExecutionData;

class ExecutableSystem;

class SymbexEngine;

class Workflow;


/**
 * TYPEDEF
 */
typedef Vector< RuntimeID >  TableOfRuntimeID_T;



class Configuration  :  public NamedElement
{

	AVM_DECLARE_UNCLONABLE_CLASS(Configuration)

public:
	/**
	 * ATTRIBUTES
	 * GLOBAL
	 */
	static const std::string SPECIFICATION_FILE_EXTENSION;

	static const std::string EXECUTABLE_FILE_EXTENSION;

	static const std::string SYMBEX_GRAPH_FILE_EXTENSION;

	static const std::string SYMBEX_SCENARII_FILE_EXTENSION;

	static const std::string GRAPHVIZ_FILE_EXTENSION;


protected :
	/**
	 * ATTRIBUTES
	 */
	SymbexEngine & mSymbexEngine;
	Workflow & mWorkflow;

	WObjectManager mWObjectManager;

	std::string mProjectSourceLocation;
	std::string mSpecificationFileLocation;

	bool mOwnedSpecificationFlag;

	std::string mOutputFilenamePattern;
	std::string mDebugFilenamePattern;

	bool mOutputExecutableEnabledGenerationFlag;
	std::string mOutputExecutableFileLocation;

	bool mOutputSymbexGraphEnabledGenerationFlag;
	std::string mOutputSymbexGraphFileLocation;

	bool mOutputSymbexScenariiEnabledGenerationFlag;
	std::string mOutputSymbexScenariiFileLocation;

	bool mDebugStageEnabledFlag;
	bool mDebugParsingStageEnabledFlag;
	bool mDebugCompilingStageEnabledFlag;
	bool mDebugLoadingStageEnabledFlag;
	bool mDebugComputingEnabledFlag;

	// Symbex Threading config
	bool mMultitaskingFlag;
	avm_uint8_t mThreadCount;

	// Shell config
	std::string mInconditionalStopMarkerLocation;


	AvmPointer< System           , DestroyElementPolicy > mSpecification;

	AvmPointer< ExecutableSystem , DestroyElementPolicy > mExecutableSystem;

	TableOfRuntimeID_T  mTableOfRID;

	ExecutionContext mMainExecutionContext;

	ListOfExecutionContext mInputContext;

	ListOfExecutionContext mTrace;


public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Configuration(SymbexEngine & aSymbexEngine, Workflow & aWorkflow);

	/**
	 * DESTRUCTOR
	 */
	virtual ~Configuration();

	void destroy();


	/**
	 * GETTER
	 * mSymbexEngine
	 */
	inline SymbexEngine & getSymbexEngine() const
	{
		return( mSymbexEngine );
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
	 * CONFIGURE
	 */
	bool configure(WObject * wfConfiguration, Configuration * prevConfiguration);

	bool configure_shell_symbex(WObject * wfConfiguration);

	bool configureFormatter(WObject * FORMAT,
			std::string & formatPattern, const std::string & id);


	/*
	 * GETTER
	 * mWorkflow
	 */
	Workflow & getWorkflow()
	{
		return( mWorkflow );
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
	const std::string & getInconditionalStopMarkerLocation() const
	{
		return( mInconditionalStopMarkerLocation );
	}


	/**
	 * mSpecificationFileLocation
	 */
	inline bool hasOwnedSpecification() const
	{
		return( mOwnedSpecificationFlag );
	}

	/**
	 * mSpecificationFileLocation
	 */
	inline const std::string & getSpecificationFileLocation() const
	{
		return( mSpecificationFileLocation );
	}

	/**
	 * GETTER
	 * OUTPUT / DEBIG FILE LOCATION
	 */
	std::string formatFileLocation(
			const std::string & aFilenamePattern, const std::string & strID,
			const std::string & strExtension = "") const;

	inline std::string formatFileLocation(bool isDebug,
			const std::string & strID, const std::string & strExtension) const
	{
		return( formatFileLocation(
				(isDebug ? mDebugFilenamePattern : mOutputFilenamePattern),
				strID, strExtension) );
	}

	inline std::string formatOutputFileLocation(
			const std::string & strID, const std::string & strExtension) const
	{
		return( formatFileLocation(
				mOutputFilenamePattern, strID, strExtension) );
	}

	inline std::string formatDebugFileLocation(
			const std::string & strID, const std::string & strExtension) const
	{
		return( formatFileLocation(
				mDebugFilenamePattern, strID, strExtension) );
	}


	/**
	 * GETTER
	 * mDebugStageEnabledFlag
	 * mDebugParsingStageEnabledFlag
	 * mDebugCompilingStageEnabledFlag
	 * mDebugLoadingEnabledFlag
	 * mDebugComputingEnabledFlag
	 */
	inline bool isDebugStageEnabled() const
	{
		return( mDebugStageEnabledFlag );
	}

	inline bool isDebugParsingStageEnabled() const
	{
		return( mDebugParsingStageEnabledFlag );
	}

	inline bool isDebugCompilingStageEnabled() const
	{
		return( mDebugCompilingStageEnabledFlag );
	}

	inline bool isDebugLoadingStageEnabled() const
	{
		return( mDebugLoadingStageEnabledFlag );
	}

	inline bool isDebugComputingStageEnabled() const
	{
		return( mDebugComputingEnabledFlag );
	}


	/*
	 * GETTER - SETTER
	 * mSpecification
	 */
	inline System & getSpecification()
	{
		return( *mSpecification );
	}

	inline const System & getSpecification() const
	{
		return( *mSpecification );
	}

	inline bool hasSpecification() const
	{
		return( mSpecification.valid() );
	}

	inline void setSpecification(System * aSpecification)
	{
		mSpecification = aSpecification;
	}


	/*
	 * GETTER - SETTER
	 * mExecutableSystem
	 */
	inline ExecutableSystem & getExecutableSystem()
	{
		return( *mExecutableSystem );
	}

	inline const ExecutableSystem & getExecutableSystem() const
	{
		return( *mExecutableSystem );
	}

//	inline bool hasExecutableSystem() const
//	{
//		return( mExecutableSystem.valid() );
//	}

	inline void setExecutableSystem(ExecutableSystem * anExecutableSystem)
	{
		mExecutableSystem = anExecutableSystem;
	}


	/**
	 * GETTER - SETTER
	 * mTableOfRID
	 */
	inline void appendRID(const RuntimeID & aRID)
	{
		mTableOfRID.append(aRID);
	}

	void destroyRIDRunningCode();

	inline const TableOfRuntimeID_T & getTableOfRID() const
	{
		return( mTableOfRID );
	}


	/*
	 * GETTER - SETTER
	 * mMainExecutionContext
	 */
	inline ExecutionContext & getMainExecutionContext()
	{
		return( mMainExecutionContext );
	}

	inline const ExecutionContext & getMainExecutionContext() const
	{
		return( mMainExecutionContext );
	}

	inline const ExecutionData & getMainExecutionData() const
	{
		return( mMainExecutionContext.refExecutionData() );
	}


	inline bool hasMainExecutionContext() const
	{
		return( mMainExecutionContext.hasExecutionData() );
	}


	inline void setMainExecutionContext(
			const ExecutionContext & anExecutionContext)
	{
		mMainExecutionContext.initialize( anExecutionContext );
	}

	inline void setMainExecutionData(const APExecutionData & anExecutionData)
	{
		mMainExecutionContext.initialize( anExecutionData , 0 , 1 );
	}


	/*
	 * GETTER - SETTER
	 * mInputContext
	 */
	inline const ListOfExecutionContext & getInputContext() const
	{
		return( mInputContext );
	}

	inline ListOfExecutionContext & getInputContext()
	{
		return( mInputContext );
	}

	inline bool hasInputContext() const
	{
		return( mInputContext.nonempty() );
	}

	inline void appendInputContext(ExecutionContext * anInputContext)
	{
		mInputContext.append( anInputContext );
	}

	/*
	 * GETTER - SETTER
	 * mTrace
	 */
	inline const ListOfExecutionContext & getTrace() const
	{
		return( mTrace );
	}

	inline ExecutionContext * getFirstTrace() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mTrace.nonempty() )
				<< "Expected a non-empty Symbex Root Execution Context List !!!"
				<< SEND_EXIT;

		return( mTrace.first() );
	}

	inline const ExecutionContext & refFirstTrace() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mTrace.nonempty() )
				<< "Expected a non-empty Symbex Root Execution Context List !!!"
				<< SEND_EXIT;

		return( *( mTrace.first() ) );
	}

	inline bool hasTrace() const
	{
		return( mTrace.nonempty() );
	}

	inline bool noTrace() const
	{
		return( mTrace.empty() );
	}

	inline void appendTrace(ExecutionContext * aTrace)
	{
		mTrace.append( aTrace );
	}

	inline void appendTrace(const ListOfExecutionContext & aTrace)
	{
		mTrace.append( aTrace );
	}


	/*
	 * SETTER
	 * mSpecification
	 * mExecutableSystem
	 * mMainExecutionContext
	 * mTrace
	 */
	void set(Configuration & aConfiguration)
	{
		mSpecification = aConfiguration.mSpecification;

		mExecutableSystem = aConfiguration.mExecutableSystem;

		setMainExecutionContext( aConfiguration.mMainExecutionContext );

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aConfiguration.mInputContext.nonempty() )
				<< "Expected a non-empty Symbex Input Execution Context List !!!"
				<< SEND_EXIT;

		mInputContext = aConfiguration.mInputContext;

		mTrace = aConfiguration.mTrace;
	}


	/**
	 * SAVING
	 */
	void saveSpecification(bool isDebug, const std::string & strID = "");
	void saveSymbexGraph(bool isDebug, const std::string & strID = "");
	void saveSymbexScenarii(bool isDebug, const std::string & strID = "");


//	static void saveSpecificationAfterCompilationStep(
//			const std::string & strPrefixName = "");
//
//
//	static void saveExecutableSpecification(
//			const std::string & strPrefixName = "");

	static void saveElementTextualView(OutStream & logger,
			const Element & anElement, const std::string & saveFileURL);

	inline static void saveElementTextualView(OutStream & logger,
			const Element * anElement, const std::string & saveFileURL)
	{
		AVM_OS_ASSERT_FATAL_NULL_POINTER_EXIT( anElement )
				<< "Element !!!"
				<< SEND_EXIT;

		if( anElement != NULL )
		{
			saveElementTextualView(logger, (* anElement), saveFileURL);
		}
	}

	// Jose Projection:
//	void saveProjection(const std::string & strPrefixName = "");
//	void saveProjectionScenarii(const std::string & strPrefixName = "");


	////////////////////////////////////////////////////////////////////////////
	// SERIALIZATION API
	////////////////////////////////////////////////////////////////////////////

	void serializeDebugExecutable(const std::string & strID);

	void serializeTextualExecutable();

	void serializeGraphizExecutable();


	void serializeTextualSymbexGraph();

	void serializeGraphizSymbexGraph();


	void serializeScenarii();


	void serializeBuildingResult();

	void serializeComputingResult();


	virtual void toStream(OutStream & os) const;

};


} /* namespace sep */

#endif /* FML_WORKFLOW_CONFIGURATION_H_ */
