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

#include <vector>


namespace sep
{

class ExecutionData;

class SymbexEngine;


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

	// CURRENT ACTIVE CONFIGURATION
	static const Configuration * CURRENT;


protected :
	/**
	 * CONFIGURATION ATTRIBUTES
	 */

	/**
	 * ATTRIBUTES
	 */
	SymbexEngine & mSymbexEngine;

	WObjectManager mWObjectManager;

	std::string mProjectSourceLocation;
	std::string mSpecificationFileLocation;

	bool mOwnedSpecificationFlag;

	std::string mOutputFilenamePattern;
	std::string mDebugFilenamePattern;

	bool mOutputExecutableEnabledGenerationFlag;
	std::string mOutputExecutableFileLocation;

	bool mOutputInitializationEnabledGenerationFlag;
	std::string mOutputInitializationFileLocation;

	bool mOutputSymbexGraphEnabledGenerationFlag;
	std::string mOutputSymbexGraphFileLocation;

	bool mOutputSymbexScenariiEnabledGenerationFlag;
	std::string mOutputSymbexScenariiFileLocation;


	bool mDebugStageEnabledFlag;

	bool mDebugParsingStageEnabledGenerationFlag;

	bool mDebugCompilingStageEnabledGenerationFlag;

	bool mDebugLoadingStageEnabledGenerationFlag;

	bool mDebugComputingStageEnabledGenerationFlag;
	std::string mDebugOutputSymbexGraphTextFileLocation;

	// Symbex config
	std::string mNameIdSeparator;

	bool mNewfreshParameterExperimentalHeightBasedUID;

	bool mNewfreshParameterNameBasedPID;
	bool mExpressionPrettyPrinterBasedFQN;
	bool mExpressionPrettyPrinterBasedNAME;

	// Symbex $time options
	std::string mTimeVariableNameID;
	std::string mTimeInitialVariableNameID;
	BF mTimeInitialVariableValue;

	std::string mTimeDeltaVariableNameID;
	std::string mTimeDeltaInitialVariableNameID;
	BF mTimeDeltaInitialVariableValue;

	// Symbex Predicate / Solver options
	bool mCheckSatisfiabilityWithSatSolverEnabled;
	bool mStronglyCheckSatisfiabilityWithSatSolverEnabled;
	bool mNodeConditionComputationEnabled;
	bool mPathConditionDisjonctionSeparationEnabled;

	// Symbex Threading config
	bool mMultitaskingFlag;
	std::uint8_t mThreadCount;

	// Console config
	std::string mConsoleVerbosity;
	std::size_t mConsoleVerbosityContextChildCount;

	// Shell config
	std::string mInconditionalStopMarkerLocation;

	// TDD config
	bool mTddRegressionTestingFlag;
	bool mTddUnitTestingFlag;
	std::string mTddReportLocation;

	// MODELS
	std::vector< System           > mSpecificationSystems;

	std::vector< ExecutableSystem > mExecutableSystems;

	AvmPointer< System           , DestroyElementPolicy > mSpecification;

	AvmPointer< ExecutableSystem , DestroyElementPolicy > mExecutableSystem;


	TableOfRuntimeID_T  mTableOfRID;

	ExecutionContext mMainExecutionContext;

	ListOfExecutionContext mInputContext;

	ListOfExecutionContext mExecutionTrace;


public :
	/**
	 * CONSTRUCTOR
	 * Default
	 */
	Configuration(SymbexEngine & aSymbexEngine);

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
	bool configure(const WObject * wfConfiguration,
			Configuration * prevConfiguration);

	// SYMBEX OPTIONS
	bool configureSymbex(const WObject * wfConfiguration);
	bool configureSymbexImpl(const WObject * wfSequenceSYMBEX);

	// CONSOLE OPTIONS
	bool configureConsole(const WObject * wfConfiguration);
	bool configureConsoleImpl(const WObject * wfSequenceCONSOLE);

	// SHELL OPTIONS
	bool configureShell(const WObject * wfConfiguration);
	bool configureShellImpl(const WObject * wfSequenceSHELL);

	// TDD OPTIONS
	bool configureTDD(const WObject * wfConfiguration);
	bool configureTDDImpl(const WObject * wfSequenceTDD);

	bool configureFormatter(const WObject * FORMAT,
			std::string & formatPattern, const std::string & id);


	/**
	 * GETTER -- SETTER
	 * mNodeConditionComputationEnabled
	 */
	inline bool isNodeConditionComputationEnabled() const
	{
		return mNodeConditionComputationEnabled;
	}

	inline void setNodeConditionComputationEnabled(bool enabled = true)
	{
		mNodeConditionComputationEnabled = enabled;
	}


	/**
	 * SETTER
	 * CURRENT ACTIVE CONFIGURATION
	 */
	void setActive() const;


	/**
	 * GETTER
	 * Symbex config
	 */
	inline const std::string & getNameIdSeparator() const
	{
		return mNameIdSeparator;
	}

	inline bool isNewfreshParameterNameBasedPID() const
	{
		return mNewfreshParameterNameBasedPID;
	}

	inline bool isNewfreshParameterExperimentalHeightBasedUID() const
	{
		return mNewfreshParameterExperimentalHeightBasedUID;
	}

	inline void setNewfreshParameterExperimentalHeightBasedUID(bool enabled)
	{
		mNewfreshParameterExperimentalHeightBasedUID = enabled;
	}

	inline bool isExpressionPrettyPrinterBasedFQN() const
	{
		return mExpressionPrettyPrinterBasedFQN;
	}

	inline bool isExpressionPrettyPrinterBasedNAME() const
	{
		return mExpressionPrettyPrinterBasedNAME;
	}


	/**
	 * Symbex Threading config
	 */
	inline bool isMultitasking() const
	{
		return( mMultitaskingFlag );
	}

	inline std::uint8_t getThreadCount() const
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
	 ***************************************************************************
	// TEST DRIVEN DEVELOPMENT
	section TDD
		report = "reportName";

		regression = true;
		unit = true;
	endsection TDD
	 ***************************************************************************
	 */
	inline bool hasTddReport() const
	{
		return( not mTddReportLocation.empty() );
	}

//	inline std::string getTddReport(
//			const std::string & aDefaultValue = "report.tdd") const
//	{
//		std::string aLocation =
//				Query::getWPropertyString(getTDD(), "report", aDefaultValue);
//
//		std::string::size_type pos = aLocation.find_last_of('.');
//		if( pos != std::string::npos )
//		{
//			aLocation.insert(pos, "_avm_" + mSEWBuildID);
//		}
//		else
//		{
//			aLocation = aLocation + "_avm_" + mSEWBuildID + ".tdd";
//		}
//
//		return( VFS::native_path(aLocation) );
//	}

	inline std::string getTddReportLocation(
			const std::string & aDefaultValue = "report.tdd") const
	{
		return( mTddReportLocation );
	}

	inline bool isTddRegressionTesting(bool aDefaultValue = false) const
	{
		return( mTddRegressionTestingFlag );
	}

	inline bool isTddUnitTesting(bool aDefaultValue = false) const
	{
		return( mTddUnitTestingFlag );
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

	inline void setSpecificationFileLocation(const std::string & fileLocation)
	{
		mSpecificationFileLocation = fileLocation;
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
	 * mDebugParsingStageEnabledGenerationFlag
	 * mDebugCompilingStageEnabledGenerationFlag
	 * mDebugLoadingEnabledFlag
	 * mDebugComputingStageEnabledGenerationFlag
	 */
	inline bool isDebugStageEnabled() const
	{
		return( mDebugStageEnabledFlag );
	}

	inline bool isDebugParsingStageEnabled() const
	{
		return( mDebugParsingStageEnabledGenerationFlag );
	}

	inline bool isDebugCompilingStageEnabled() const
	{
		return( mDebugCompilingStageEnabledGenerationFlag );
	}

	inline bool isDebugLoadingStageEnabled() const
	{
		return( mDebugLoadingStageEnabledGenerationFlag );
	}

	inline bool isDebugComputingStageEnabled() const
	{
		return( mDebugComputingStageEnabledGenerationFlag );
	}


	/**
	 * FACTORY - GETTER
	 * mExecutableSystems
	 */
	template<typename... _Args>
	System & newSpecificationSystem( _Args && ... __args )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mSpecificationSystems.size() < 7 )
				<< "Out Of Memory for Table of SpecificationSystem !!!";

		mSpecificationSystems.emplace_back( __args ... ) ;

		return( mSpecificationSystems.back() );
	}

	inline std::vector< System > & getSpecificationSystems()
	{
		return( mSpecificationSystems );
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


	/**
	 * FACTORY - GETTER
	 * mExecutableSystems
	 */
	template<typename... _Args>
	ExecutableSystem & newExecutableSystem( _Args && ... __args )
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mSpecificationSystems.size() < 7 )
				<< "Out Of Memory for Table of ExecutableSystem !!!";

		return( mExecutableSystems.emplace_back( __args ... ) );

//		return( mExecutableSystems.back() );
	}

	inline std::vector< ExecutableSystem > & getExecutableSystems()
	{
		return( mExecutableSystems );
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
		return( mMainExecutionContext.getExecutionData() );
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

	inline void setMainExecutionData(const ExecutionData & anExecutionData)
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

	inline ExecutionContext & getFirstInputContext()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mInputContext.nonempty() )
				<< "Expected a non-empty Symbex Input Execution Context List !!!"
				<< SEND_EXIT;

		return( *( mInputContext.first() ) );
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
	 * mExecutionTrace
	 */
	inline const ListOfExecutionContext & getExecutionTrace() const
	{
		return( mExecutionTrace );
	}

	inline ExecutionContext & getFirstExecutionTrace()
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mExecutionTrace.nonempty() )
				<< "Expected a non-empty Symbex Root Execution Context List !!!"
				<< SEND_EXIT;

		return( *( mExecutionTrace.first() ) );
	}

	inline const ExecutionContext & getFirstExecutionTrace() const
	{
		AVM_OS_ASSERT_FATAL_ERROR_EXIT( mExecutionTrace.nonempty() )
				<< "Expected a non-empty Symbex Root Execution Context List !!!"
				<< SEND_EXIT;

		return( *( mExecutionTrace.first() ) );
	}

	inline bool hasExecutionTrace() const
	{
		return( mExecutionTrace.nonempty() );
	}

	inline bool noExecutionTrace() const
	{
		return( mExecutionTrace.empty() );
	}

	inline void appendExecutionTrace(ExecutionContext * aTrace)
	{
		mExecutionTrace.append( aTrace );
	}

	inline void appendExecutionTrace(const ListOfExecutionContext & aTrace)
	{
		mExecutionTrace.append( aTrace );
	}


	/*
	 * SETTER
	 * mSpecification
	 * mExecutableSystem
	 * mMainExecutionContext
	 * mExecutionTrace
	 */
	inline void reset(Configuration & aConfiguration)
	{
		mSpecification = aConfiguration.mSpecification;

		mExecutableSystem = aConfiguration.mExecutableSystem;

		setMainExecutionContext( aConfiguration.mMainExecutionContext );

		AVM_OS_ASSERT_FATAL_ERROR_EXIT( aConfiguration.mInputContext.nonempty() )
				<< "Expected a non-empty Symbex Input Execution Context List !!!"
				<< SEND_EXIT;

		mInputContext = aConfiguration.mInputContext;

		mExecutionTrace = aConfiguration.mExecutionTrace;
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

		if( anElement != nullptr )
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

	void serializeDebugExecutable(const std::string & strID) const;

	void serializeTextualExecutable() const;

	void serializeGraphizExecutable() const;


	void serializeTextualSymbexGraph() const;

	void serializeGraphizSymbexGraph() const;


	void serializeScenarii() const;


	void serializeBuildingResult() const;

	void serializeLoadingResult() const;

	void serializeComputingResult() const;


	virtual void toStream(OutStream & os) const override;

};


} /* namespace sep */

#endif /* FML_WORKFLOW_CONFIGURATION_H_ */
