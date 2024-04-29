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

#include "Configuration.h"

#include <computer/PathConditionProcessor.h>

#include  <famcore/serializer/GraphVizExecutionGraphSerializer.h>
#include  <famcore/serializer/GraphVizStatemachineSerializer.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/workflow/Query.h>

#include <sew/SymbexEngine.h>
#include <sew/WorkflowParameter.h>

#include <solver/api/SolverFactory.h>

#include <util/avm_util.h>
#include <util/avm_vfs.h>

#include <boost/format.hpp>


namespace sep
{


/**
 * ATTRIBUTES
 * GLOBAL
 */
const std::string Configuration::SPECIFICATION_FILE_EXTENSION   = ".xlia";

const std::string Configuration::EXECUTABLE_FILE_EXTENSION      = ".fexe";

const std::string Configuration::SYMBEX_GRAPH_FILE_EXTENSION    = ".fet";

const std::string Configuration::SYMBEX_SCENARII_FILE_EXTENSION = ".fscn";

const std::string Configuration::GRAPHVIZ_FILE_EXTENSION        = ".gv";

// CURRENT ACTIVE CONFIGURATION
const Configuration * Configuration::CURRENT = nullptr;


/**
 * CONSTRUCTOR
 * Default
 */
Configuration::Configuration(SymbexEngine & aSymbexEngine)
: NamedElement( CLASS_KIND_T( Configuration ) , aSymbexEngine ),
mSymbexEngine( aSymbexEngine ),

mWObjectManager( WObject::FML_FQN_ROOT ),
mProjectSourceLocation( ),
mSpecificationFileLocation( ),

mOwnedSpecificationFlag( false ),

mOutputFilenamePattern( "output_%1%" ),
mDebugFilenamePattern ( "debug_%1%"  ),

mOutputExecutableEnabledGenerationFlag( false ),
mOutputExecutableFileLocation( ),

mOutputInitializationEnabledGenerationFlag( false ),
mOutputInitializationFileLocation( ),

mOutputSymbexGraphEnabledGenerationFlag( false ),
mOutputSymbexGraphFileLocation( ),

mOutputSymbexScenariiEnabledGenerationFlag( false ),
mOutputSymbexScenariiFileLocation( ),

mDebugStageEnabledFlag( false ),
mDebugParsingStageEnabledGenerationFlag  ( false ),
mDebugCompilingStageEnabledGenerationFlag( false ),
mDebugLoadingStageEnabledGenerationFlag  ( false ),

mDebugComputingStageEnabledGenerationFlag( false ),
mDebugOutputSymbexGraphTextFileLocation( ),

// Symbex config
mNameIdSeparator( "#" ),
mNewfreshParameterExperimentalHeightBasedUID( false ),
mNewfreshParameterNameBasedPID   ( true ),
mExpressionPrettyPrinterBasedFQN ( true  ),
mExpressionPrettyPrinterBasedNAME( false ),

// Symbex $time options
mTimeVariableNameID( PropertyPart::VAR_ID_TIME ),
mTimeInitialVariableNameID( PropertyPart::VAR_ID_TIME_INITIAL ),
mTimeInitialVariableValue( PropertyPart::VAR_TIME_INITIAL_VALUE ),

mTimeDeltaVariableNameID( PropertyPart::VAR_ID_DELTA_TIME ),
mTimeDeltaInitialVariableNameID( PropertyPart::VAR_ID_DELTA_TIME_INITIAL ),
mTimeDeltaInitialVariableValue( PropertyPart::VAR_DELTA_TIME_INITIAL_VALUE ),

// Symbex Predicate / Solver options
mCheckSatisfiabilityWithSatSolverEnabled( false ),
mStronglyCheckSatisfiabilityWithSatSolverEnabled( false ),
mNodeConditionComputationEnabled( false ),
mPathConditionDisjonctionSeparationEnabled( false ),

// Symbex Threading config
mMultitaskingFlag( false ),
mThreadCount( 1 ),

// Console config
mConsoleVerbosity( "MEDIUM" ),
mConsoleVerbosityContextChildCount( 42 ),
// Shell config
mInconditionalStopMarkerLocation( "stop.sew" ),

// TDD config
mTddRegressionTestingFlag( false ),
mTddUnitTestingFlag( false ),
mTddReportLocation( ),

// MODELS
mSpecificationSystems( ),
mExecutableSystems( ),

mSpecification( nullptr ),
mExecutableSystem( nullptr ),

mTableOfRID( ),
mMainExecutionContext( ),
mInputContext( ),
mExecutionTrace( )
{
	mSpecificationSystems.reserve( 7 );

	mExecutableSystems.reserve( 7 );
}

/**
 * DESTRUCTOR
 */
Configuration::~Configuration()
{
	destroy();
}

void Configuration::destroy()
{
	if( mOwnedSpecificationFlag )
	{
		reportInstanceCounterUsage(AVM_OS_LOG, "Configuration::destroy");

		if( mExecutionTrace.populated() )
		{
			ExecutionContext * itEC;
			while( mExecutionTrace.nonempty() )
			{
				mExecutionTrace.pop_last_to( itEC );
				mExecutionTrace.remove( itEC );
				sep::destroyElement( itEC );
			}
		}
		else if( mExecutionTrace.nonempty() )
		{
			sep::destroyElement( mExecutionTrace.pop_last() );
		}

		mMainExecutionContext.destroy();

		// Attention:> Necessaire pour briser des references circulaires !!!!
		destroyRIDRunningCode();

		mExecutableSystem.destroy();

		reportInstanceCounterUsage(AVM_OS_LOG, "~Configuration::destroy:> "
				"after destruction of executable & execution context");

		mSpecification.destroy();

		reportInstanceCounterUsage(AVM_OS_LOG, "~Configuration::destroy:> "
				"after destruction of specification");
	}
}

// Attention:> Necessaire pour briser des references circulaires !!!!
void Configuration::destroyRIDRunningCode()
{
	for( auto & itRID : mTableOfRID )
	{
		itRID.finalize();
	}

//	mTableOfRID.clear();
}



/**
 * CONFIGURE
 */
/*
director exploration 'as main execution objective' {
	...
	project 'path of input model' [
		source = "model/absolute/or/relative/path"
		model  = "model.xlia"
	] // end project
	...
	output 'standard analysis file' [
		filename = 'model_%1%'
		specification = 'model.xlia'
		executable = 'model.fexe'
		initialization = 'model_init.fet'
		scenarii = 'model.fscn'
	] // end output
	debug 'analysis file at different stage' [
		filename = 'model_%1%'
		parsing = 'model_parsed.xlia'
		executable = 'model.fexe'
		execution = 'model.fet'
	] // end debug
	...
}
*/
bool Configuration::configure(
		const WObject * wfConfiguration, Configuration * prevConfiguration)
{
	bool isOK = configureConsole(wfConfiguration);

	isOK = configureShell(wfConfiguration)
		&& isOK;

	isOK = configureTDD(wfConfiguration)
		&& isOK;


	if( not configureSymbex(wfConfiguration) )
	{
		AVM_OS_ERROR_ALERT << "SymbexEngine:> "
					"the FAMs Controller Unit initialization failed !!!"
				<< SEND_ALERT;

		return( false );
	}


	const WObject * aSECTION = Query::getWSequenceOrElse(
			wfConfiguration, "project", "SPECIFICATION");
	if( aSECTION != WObject::_NULL_ )
	{
		mProjectSourceLocation =
				Query::getRegexWPropertyString(aSECTION,
						OR_WID2("source", "src"), VFS::WorkspaceSourcePath);

		mProjectSourceLocation = VFS::native_path(
				mProjectSourceLocation, VFS::WorkspaceRootPath);

		mSpecificationFileLocation =
				Query::getRegexWPropertyString(
						aSECTION, OR_WID2("model", "main"), "");

		bool ignoreModel = Query::getWPropertyBoolean(aSECTION, "ignore", false);

		mOwnedSpecificationFlag = (not mSpecificationFileLocation.empty());

		if( mOwnedSpecificationFlag )
		{
			mOutputFilenamePattern = mDebugFilenamePattern =
					(VFS::basename(mSpecificationFileLocation) + "_%1%");

			mSpecificationFileLocation = VFS::native_path(
					mSpecificationFileLocation, mProjectSourceLocation);

			OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_COUT )
					<< _SEW_ << "Checking the specification file: \""
					<< VFS::relativeWorkspacePath( mSpecificationFileLocation )
					<< "\" ...";

			AVM_OS_LOG << _SEW_ << "Checking the specification ..."
					<< std::endl
					<< _SEW_ << "File location:> "
					<< VFS::relativeWorkspacePath( mSpecificationFileLocation );

			if( ignoreModel )
			{
				//!! NOTHING TO DO for raw text model
			}
			else if( VFS::checkReadingFile(mSpecificationFileLocation) )
			{
				OS_VERBOSITY_MINIMUM_OR_DEBUG( AVM_OS_COUT )
						<< " ==> DONE"  << std::endl;

				AVM_OS_LOG << " ==> DONE"  << std::endl;
			}
			else
			{
				mOwnedSpecificationFlag = false;

				AVM_OS_COUT << EOL_TAB << " ==> FAILED :> "
						<< "This file doesn't exist or is not readable !!!"
						<< std::endl;

				return( false );
			}
		}
	}
	else if( prevConfiguration != nullptr )
	{
		mProjectSourceLocation     = prevConfiguration->mProjectSourceLocation;
		mSpecificationFileLocation = prevConfiguration->mSpecificationFileLocation;

		mOutputFilenamePattern     = prevConfiguration->mOutputFilenamePattern;
		mDebugFilenamePattern      = prevConfiguration->mDebugFilenamePattern;
	}

	aSECTION = Query::getRegexWSequence(
			wfConfiguration, OR_WID2("output", "OUTPUT"));
	if( aSECTION != WObject::_NULL_ )
	{
		if( configureFormatter(aSECTION, mOutputFilenamePattern, "filename" ) )
		{
			mOutputFilenamePattern = VFS::native_path(
					mOutputFilenamePattern, VFS::WorkspaceOutputPath);

			// Output Executable
			mOutputExecutableFileLocation =
					Query::getWPropertyString(aSECTION, "executable", "");

			mOutputExecutableEnabledGenerationFlag =
					(not mOutputExecutableFileLocation.empty());
			if( mOutputExecutableEnabledGenerationFlag )
			{
				mOutputExecutableFileLocation = VFS::native_path(
					mOutputExecutableFileLocation, VFS::WorkspaceOutputPath);
			}
			else
			{
				mOutputExecutableFileLocation =
						mOutputFilenamePattern + EXECUTABLE_FILE_EXTENSION;
			}

			// Output Initialization
			mOutputInitializationFileLocation =
					Query::getWPropertyString(aSECTION, "initialization", "");

			mOutputInitializationEnabledGenerationFlag =
					(not mOutputInitializationFileLocation.empty());
			if( mOutputInitializationEnabledGenerationFlag )
			{
				mOutputInitializationFileLocation = VFS::native_path(
					mOutputInitializationFileLocation, VFS::WorkspaceOutputPath);
			}
			else
			{
				mOutputInitializationFileLocation =
						mOutputFilenamePattern + SYMBEX_GRAPH_FILE_EXTENSION;
			}

			// Output SymbexGraph
			mOutputSymbexGraphFileLocation =
					Query::getRegexWPropertyString(aSECTION, "graph(viz)?", "");

			mOutputSymbexGraphEnabledGenerationFlag =
					(not mOutputSymbexGraphFileLocation.empty());
			if( mOutputSymbexGraphEnabledGenerationFlag )
			{
				mOutputSymbexGraphFileLocation = VFS::native_path(
					mOutputSymbexGraphFileLocation, VFS::WorkspaceOutputPath);
			}
			else
			{
				mOutputSymbexGraphFileLocation = formatFileLocation(
						false, "graph", GRAPHVIZ_FILE_EXTENSION);
			}

			// Output Symbex Scenaii
			mOutputSymbexScenariiFileLocation =
					Query::getWPropertyString(aSECTION, "scenarii", "");

			mOutputSymbexScenariiEnabledGenerationFlag =
					(not mOutputSymbexScenariiFileLocation.empty());
			if( mOutputSymbexScenariiEnabledGenerationFlag )
			{
				mOutputSymbexScenariiFileLocation = VFS::native_path(
				mOutputSymbexScenariiFileLocation, VFS::WorkspaceOutputPath);
			}
			else
			{
				mOutputSymbexScenariiFileLocation =
						mOutputFilenamePattern +  SYMBEX_SCENARII_FILE_EXTENSION;
			}
		}
		else
		{
			AVM_OS_WARN << "Configuration::configureWObject:> "
					"Failed to configure Output Filename Pattern < "
					<< mOutputFilenamePattern << " > !" << std::endl;

			return( false );
		}
	}

	aSECTION = Query::getRegexWSequence(wfConfiguration,
			OR_WID2("debug", "DEBUG"), aSECTION);
	if( aSECTION != WObject::_NULL_ )
	{
		mDebugStageEnabledFlag = true;

		if( configureFormatter(aSECTION, mDebugFilenamePattern, "filename" ) )
		{
			mDebugFilenamePattern = VFS::native_path(
					mDebugFilenamePattern, VFS::WorkspaceDebugPath);
		}
		else
		{
			AVM_OS_WARN << "Configuration::configureWObject:> "
					"Failed to configure Debug Filename Pattern < "
					<< mDebugFilenamePattern << " > !" << std::endl;

			return( false );
		}

		mDebugParsingStageEnabledGenerationFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "parsing");

		mDebugCompilingStageEnabledGenerationFlag = mDebugStageEnabledFlag
				&& Query::hasRegexWPropertyString(aSECTION, "compilation");

		mDebugLoadingStageEnabledGenerationFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "loading");

		// Debug Output Textual SymbexGraph
		mDebugOutputSymbexGraphTextFileLocation =
				Query::getWPropertyString(aSECTION, "execution", "");

		mDebugComputingStageEnabledGenerationFlag = mDebugStageEnabledFlag
				&& (not mDebugOutputSymbexGraphTextFileLocation.empty());
		if( mDebugComputingStageEnabledGenerationFlag )
		{
			mDebugOutputSymbexGraphTextFileLocation = VFS::native_path(
					mDebugOutputSymbexGraphTextFileLocation,
					VFS::WorkspaceDebugPath);
		}
		else
		{
			mDebugOutputSymbexGraphTextFileLocation = formatFileLocation(
					true, "graph", GRAPHVIZ_FILE_EXTENSION);
		}

	}

	return( isOK );
}


bool Configuration::configureFormatter(const WObject * FORMAT,
		std::string & formatPattern, const std::string & id)
{
	formatPattern = Query::getWPropertyString(FORMAT, id, formatPattern);

	try
	{
		boost::format formatter(formatPattern);
	}
	catch(const boost::io::bad_format_string & bfs)
	{
		Query::reportErrorAttribute(FORMAT, id, bfs.what());

		return( false );
	}

	return( true );
}


/**
 * SYMBEX OPTIONS
 */
bool Configuration::configureSymbex(const WObject * wfConfiguration)
{
	bool isOK = true;

	const WObject * parentSYMBEX = Query::getparentRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_SYMBEX_REGEX_ID);

	if( parentSYMBEX != WObject::_NULL_ )
	{
		isOK = configureSymbexImpl(parentSYMBEX);
	}

	const WObject * localSYMBEX = Query::getRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_SYMBEX_REGEX_ID);

	if( (localSYMBEX != WObject::_NULL_) &&  (localSYMBEX != parentSYMBEX) )
	{
		isOK = configureSymbexImpl(localSYMBEX)
			|| isOK;
	}

	return( isOK );
}

bool Configuration::configureSymbexImpl(const WObject * wfSequenceSYMBEX)
{
	// NAME_ID SEPARATOR
	mNameIdSeparator = Query::getRegexWPropertyString(wfSequenceSYMBEX,
			CONS_WID3("name", "id", "separator"), mNameIdSeparator);

	RuntimeID::NAME_ID_SEPARATOR = mNameIdSeparator;

	RuntimeID::BASENAME = RuntimeID::BASENAME_PREFIX + mNameIdSeparator;

	RuntimeID::BASENAME_PARENT =
			RuntimeID::BASENAME_PARENT_PREFIX + mNameIdSeparator;

	// PRETTY PRINTING CONFIG
	mNewfreshParameterExperimentalHeightBasedUID =
			Query::getRegexWPropertyBoolean(wfSequenceSYMBEX,
					CONS_WID4("newfresh", "param(eter)?", "height", "uid"),
					mNewfreshParameterExperimentalHeightBasedUID);

	// PRETTY PRINTING CONFIG
	mNewfreshParameterNameBasedPID =
			Query::getRegexWPropertyBoolean(wfSequenceSYMBEX,
					CONS_WID4("newfresh", "param(eter)?", "(name|id)", "pid"),
					mNewfreshParameterNameBasedPID);

	mExpressionPrettyPrinterBasedNAME =
			Query::getRegexWPropertyBoolean(wfSequenceSYMBEX,
					CONS_WID4("pretty", "printer", "var(iable)?", "(name|id)"),
					mExpressionPrettyPrinterBasedNAME);

	mExpressionPrettyPrinterBasedFQN =
			(not mExpressionPrettyPrinterBasedNAME);

	// SYMBEX $TIME OPTIONS
	mTimeVariableNameID =
			Query::getRegexWPropertyString(wfSequenceSYMBEX,
					CONS_WID3("time", "name", "id"),
					mTimeVariableNameID);

	mTimeInitialVariableValue =
			Query::getRegexWPropertyValue(wfSequenceSYMBEX,
					CONS_WID3("time", "initial", "value"),
					mTimeInitialVariableValue);


	mTimeDeltaVariableNameID =
			Query::getRegexWPropertyString(wfSequenceSYMBEX,
					CONS_WID3("delta", "name", "id"),
					mTimeDeltaVariableNameID);

	mTimeDeltaInitialVariableValue =
			Query::getRegexWPropertyValue(wfSequenceSYMBEX,
					CONS_WID3("delta", "initial", "value"),
					mTimeDeltaInitialVariableValue);

	// SYMBEX PREDICATE / SOLVER OPTIONS
	mStronglyCheckSatisfiabilityWithSatSolverEnabled =
		SolverDef::DEFAULT_SOLVER_USAGE_FLAG =
			Query::getRegexWPropertyBoolean(
				wfSequenceSYMBEX,
				OR_WID2(
					CONS_WID5("strongly", "check", "satisfiability", "solver", "enabled"),
					CONS_WID5("strongly", "check", "path", "condition", "satisfiability")),
					mStronglyCheckSatisfiabilityWithSatSolverEnabled);

	mCheckSatisfiabilityWithSatSolverEnabled =
		SolverDef::DEFAULT_SOLVER_USAGE_FLAG =
			Query::getRegexWPropertyBoolean(
				wfSequenceSYMBEX,
				OR_WID2(
					CONS_WID4("check", "satisfiability", "solver", "enabled"),
					CONS_WID4("check", "path", "condition", "satisfiability")),
				mCheckSatisfiabilityWithSatSolverEnabled ||
				mStronglyCheckSatisfiabilityWithSatSolverEnabled);


	mNodeConditionComputationEnabled =
			Query::getRegexWPropertyBoolean(wfSequenceSYMBEX,
					CONS_WID3("node", "condition", "enabled"),
					mNodeConditionComputationEnabled);

	mPathConditionDisjonctionSeparationEnabled =
			Query::getWPropertyBoolean(wfSequenceSYMBEX,
					"separation_of_pc_disjunction",
					mPathConditionDisjonctionSeparationEnabled);


	std::string solverKind = Query::getRegexWPropertyString(
			wfSequenceSYMBEX, CONS_WID2("constraint", "solver"), "USER_UNDEFINED");

	SolverDef::DEFAULT_SOLVER_KIND = SolverDef::toSolver(solverKind,
			SolverDef::SOLVER_CVC_KIND);

	// SETTING DEFAULT SOLVER INSTANCE
	SolverFactory::load();

AVM_IF_DEBUG_ENABLED
	AVM_OS_LOG << _SEW_ << "The default solver: < checksat="
			<< ( SolverDef::DEFAULT_SOLVER_USAGE_FLAG ? "true" : "false" )
			<< " , " << solverKind << " > |=> "
			<< SolverDef::strSolver(SolverDef::DEFAULT_SOLVER_KIND)
			<< std::endl;
AVM_ENDIF_DEBUG_ENABLED

	// Multithreading options
	mMultitaskingFlag = Query::getWPropertyBoolean(
			wfSequenceSYMBEX, "multitasking", mMultitaskingFlag);

	mThreadCount = Query::getWPropertyInt(wfSequenceSYMBEX, "thread", mThreadCount);


	std::string evalMode = Query::getWPropertyString(wfSequenceSYMBEX, "mode", "");

AVM_IF_DEBUG_ENABLED
	AVM_OS_LOG << _SEW_ << "Computing resource: < multitasking="
			<< ( ( mMultitaskingFlag ) ? "true" : "false" )
			<< " , thread=" << static_cast< unsigned int >( mThreadCount )
			<< " >" << std::endl;
AVM_ENDIF_DEBUG_ENABLED

	return( true );
}


/**
 * SHELL OPTIONS
 */
bool Configuration::configureConsole(const WObject * wfConfiguration)
{
	bool isOK = true;

	const WObject * parentCONSOLE = Query::getparentRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_CONSOLE_REGEX_ID);

	if( parentCONSOLE != WObject::_NULL_ )
	{
		isOK = configureConsoleImpl(parentCONSOLE);
	}

	const WObject * localCONSOLE = Query::getRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_CONSOLE_REGEX_ID);

	if( (localCONSOLE != WObject::_NULL_) &&  (localCONSOLE != parentCONSOLE) )
	{
		isOK = configureConsoleImpl(localCONSOLE)
			|| isOK;
	}

	return( isOK );
}

bool Configuration::configureConsoleImpl(const WObject * wfSequenceCONSOLE)
{
	// Set console verbosity level
	mConsoleVerbosity = Query::getRegexWPropertyString(
			wfSequenceCONSOLE, "verbos(ity|e)", mConsoleVerbosity);

	mConsoleVerbosityContextChildCount =
			Query::getWPropertyLong(wfSequenceCONSOLE, "ec_size",
					mConsoleVerbosityContextChildCount);


	return( true );
}

/**
 * SHELL OPTIONS
 */
bool Configuration::configureShell(const WObject * wfConfiguration)
{
	bool isOK = true;

	const WObject * parentSHELL = Query::getparentRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_SHELL_REGEX_ID);

	if( parentSHELL != WObject::_NULL_ )
	{
		isOK = configureShellImpl(parentSHELL);
	}

	const WObject * localSHELL = Query::getRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_SHELL_REGEX_ID);

	if( (localSHELL != WObject::_NULL_) &&  (localSHELL != parentSHELL) )
	{
		isOK = configureShellImpl(localSHELL)
			|| isOK;
	}

	return( isOK );
}

bool Configuration::configureShellImpl(const WObject * wfSequenceSHELL)
{
	mInconditionalStopMarkerLocation = Query::getWPropertyString(
			wfSequenceSHELL, "stop", mInconditionalStopMarkerLocation);

	if( not mInconditionalStopMarkerLocation.empty() )
	{
		mInconditionalStopMarkerLocation =
				VFS::native_path(mInconditionalStopMarkerLocation);

		mInconditionalStopMarkerLocation = VFS::native_path(
				mInconditionalStopMarkerLocation, VFS::WorkspaceOutputPath);
	}

	return( true );
}

/**
 * TDD OPTIONS
 */
//section TDD
//	@report = "avm.tdd";
//
//	@regression = true;
//	@unit = true;
//endsection TDD

bool Configuration::configureTDD(const WObject * wfConfiguration)
{
	bool isOK = true;

	const WObject * parentTDD = Query::getparentRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_TDD_REGEX_ID);

	if( parentTDD != WObject::_NULL_ )
	{
		isOK = configureTDDImpl(parentTDD);
	}

	const WObject * localTDD = Query::getRegexWSequence(
			wfConfiguration, WorkflowParameter::SECTION_TDD_REGEX_ID);

	if( (localTDD != WObject::_NULL_) &&  (localTDD != parentTDD) )
	{
		isOK = configureTDDImpl(localTDD)
			|| isOK;
	}

	return( isOK );
}

bool Configuration::configureTDDImpl(const WObject * wfSequenceTDD)
{
	mTddRegressionTestingFlag = Query::getWPropertyBoolean(
			wfSequenceTDD, "regression", mTddRegressionTestingFlag);

	mTddUnitTestingFlag = Query::getWPropertyBoolean(
			wfSequenceTDD, "unit", mTddUnitTestingFlag);

	mTddReportLocation = Query::getWPropertyString(
			wfSequenceTDD, "report", mTddReportLocation);
	if( not mTddReportLocation.empty() )
	{
		mTddReportLocation = VFS::native_path(
				mTddReportLocation, VFS::ProjectTddPath);
	}

	return( true );
}


/**
 * SETTER
 * CURRENT ACTIVE CONFIGURATION
 */
void Configuration::setActive() const
{
	CURRENT = this;

	avm_setExecVerbosityLevel( mConsoleVerbosity );

	NamedElement::NAME_ID_SEPARATOR = mNameIdSeparator;

	BaseInstanceForm::EXPRESSION_PRETTY_PRINTER_FQN_BASED =
			mExpressionPrettyPrinterBasedFQN;

	AvmCode::EXPRESSION_PRETTY_PRINTER_BASED_FQN =
			mExpressionPrettyPrinterBasedFQN;


	PropertyPart::VAR_ID_TIME = mTimeVariableNameID;

	PropertyPart::VAR_TIME_INITIAL_VALUE = mTimeInitialVariableValue;


	PropertyPart::VAR_ID_DELTA_TIME = mTimeDeltaVariableNameID;

	PropertyPart::VAR_DELTA_TIME_INITIAL_VALUE = mTimeDeltaInitialVariableValue;


	PathConditionProcessor::CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED =
			mCheckSatisfiabilityWithSatSolverEnabled;

	PathConditionProcessor::STRONGLY_CHECK_SATISFIABILITY_WITH_SATSOLVER_ENABLED =
			mStronglyCheckSatisfiabilityWithSatSolverEnabled;

	PathConditionProcessor::NODE_CONDITION_COMPUTATION_ENABLED =
			mNodeConditionComputationEnabled;

	PathConditionProcessor::PATH_CONDIDITON_DISJONCTION_SEPARATION_ENABLED =
			mPathConditionDisjonctionSeparationEnabled;

	ExecutionContext::EXECUTION_CONTEXT_CHILD_TRACE_MAX =
			mConsoleVerbosityContextChildCount;
}



/**
 * GETTER
 * OUTPUT / DEBUG FILE LOCATION
 */
std::string Configuration::formatFileLocation(
		const std::string & aFilenamePattern,
		const std::string & strID, const std::string & strExtension) const
{
	boost::format locationFormatter(aFilenamePattern);

	locationFormatter.exceptions( boost::io::no_error_bits );

	if( strExtension.empty() )
	{
		return( ( locationFormatter % strID ).str() );
	}
	else
	{
		return( (OSS() << (locationFormatter % strID) << strExtension).str() );
	}
}


/**
 * SAVING
 */
void Configuration::saveSpecification(bool isDebug, const std::string & strID)
{
	std::string saveFileLocation = formatFileLocation(
			isDebug, strID, SPECIFICATION_FILE_EXTENSION);

	if( isDebug )
	{
		AVM_OS_CLOG << _DBG_
			<< "Saving of the Specification in text format --> "
			<< strID << std::endl;
	}
	else
	{
		AVM_OS_LOG << _SEW_
			<< "Saving of the Specification in text format --> "
			<< strID << std::endl;
	}

	Configuration::saveElementTextualView(AVM_OS_LOG,
			getSpecification(), saveFileLocation);
}

void Configuration::saveSymbexGraph(bool isDebug, const std::string & strID)
{
	std::string saveFileLocation = formatFileLocation(
			isDebug, strID, SYMBEX_GRAPH_FILE_EXTENSION);
}

void Configuration::saveSymbexScenarii(bool isDebug, const std::string & strID)
{
	std::string saveFileLocation = formatFileLocation(
			isDebug, strID, SYMBEX_SCENARII_FILE_EXTENSION);
}


/**
 * save Element as textual view
 *
 */
void Configuration::saveElementTextualView(OutStream & logger,
		const Element & anElement, const std::string & saveFileLocation)
{
	ScopeNewIndent scope( logger , AVM_TAB1_INDENT );

	logger << TAB << "path: "
			<< VFS::relativeWorkspacePath( saveFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(saveFileLocation, std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream out(resultStream);
		anElement.serialize(out);

		resultStream.close();

		logger << "OK" << std::endl ;
	}
	else
	{
		logger << std::endl << TAB
				<< "    KO : Failed to open this file in write mode"
				<< std::endl;
	}
}


////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////

void Configuration::serializeDebugExecutable(const std::string & strID) const
{
	std::string saveFileLocation = formatFileLocation(
			true, strID, EXECUTABLE_FILE_EXTENSION);

	AVM_OS_CLOG << _DBG_
		<< "Saving of the Executable in text format --> "
		<< strID << std::endl;

	Configuration::saveElementTextualView(AVM_OS_LOG,
			mExecutableSystem, saveFileLocation);
}

void Configuration::serializeTextualExecutable() const
{
	AVM_OS_LOG << _SEW_
			<< "Saving of the Executable in text format" << std::endl;

	Configuration::saveElementTextualView(AVM_OS_LOG,
			mExecutableSystem, mOutputExecutableFileLocation);
}


void Configuration::serializeGraphizExecutable() const
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	std::string saveFileLocation = VFS::replace_extension(
			mOutputExecutableFileLocation, GRAPHVIZ_FILE_EXTENSION);

	AVM_OS_LOG << _SEW_
			<< "Saving of the specification representation "
			"in GraphViz format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath( saveFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(saveFileLocation, std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream out(resultStream, AVM_SPC_INDENT);

		GraphVizStatemachineSerializer::format(
			mSymbexEngine.getControllerUnitManager(), out, getSpecification());

		resultStream.close();

		AVM_OS_LOG << "OK" << std::endl ;
	}
	else
	{
		AVM_OS_LOG << std::endl << TAB
				<< "    KO : Failed to open this file in write mode"
				<< std::endl;
	}
}

/**
 * serialize Textual SymbexGraph
 */
void Configuration::serializeTextualSymbexGraph() const
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the trace of the execution specification "
			"representation in textual format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath( mDebugOutputSymbexGraphTextFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(mDebugOutputSymbexGraphTextFileLocation,
			std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream out(resultStream, AVM_SPC_INDENT);

		for( const auto & itEC : getExecutionTrace() )
		{
			itEC->serialize(out);
		}

		resultStream.close();

		AVM_OS_LOG << "OK" << std::endl;
	}
	else
	{
		AVM_OS_LOG << std::endl << TAB
				<< "    KO : Failed to open this file in write mode"
				<< std::endl;
	}

	if( hasMainExecutionContext() )
	{
		std::string saveFileLocation = formatFileLocation(
				true, "graph_tec", SYMBEX_GRAPH_FILE_EXTENSION);

		saveElementTextualView(AVM_OS_LOG,
				getMainExecutionContext(), saveFileLocation);
	}
}

/**
 * serialize Graphiz SymbexGraph
 */
void Configuration::serializeGraphizSymbexGraph() const
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the SHELL trace of the execution specification "
			"representation in GraphViz format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath( mOutputSymbexGraphFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(mOutputSymbexGraphFileLocation, std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream out(resultStream, AVM_SPC_INDENT);

		GraphVizExecutionGraphSerializer::format(
				mSymbexEngine.getControllerUnitManager(),
				out, getExecutionTrace());

		resultStream.close();

		AVM_OS_LOG << "OK" << std::endl ;
	}
	else
	{
		AVM_OS_LOG << std::endl << TAB
				<< "    KO : Failed to open this file in write mode"
				<< std::endl;
	}
}


void Configuration::serializeScenarii() const
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the trace of the execution specification "
			"representation in textual format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath(mOutputSymbexScenariiFileLocation)
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(mOutputSymbexScenariiFileLocation,
			std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream out(resultStream, AVM_FSCN_INDENT);

		for( const auto & itEC : getExecutionTrace() )
		{
			itEC->toFscn(out, ExecutionData::_NULL_);
		}

		resultStream.close();

		AVM_OS_LOG << "OK" << std::endl ;
	}
	else
	{
		AVM_OS_LOG << std::endl << TAB
				<< "    KO : Failed to open this file in write mode"
				<< std::endl;
	}
}

/**
 * Serialization building stage
 */
void Configuration::serializeBuildingResult() const
{
	if( mOutputExecutableEnabledGenerationFlag )
	{
		serializeTextualExecutable();

		serializeGraphizExecutable();
	}
}

/**
 * Serialization loading stage
 */
void Configuration::serializeLoadingResult() const
{
	if( mOutputInitializationEnabledGenerationFlag
		&& hasMainExecutionContext() )
	{
		saveElementTextualView(AVM_OS_LOG,
				getMainExecutionContext(), mOutputInitializationFileLocation);
	}
}

/**
 * Serialization computing stage
 */
void Configuration::serializeComputingResult() const
{
AVM_IF_DEBUG_FLAG_AND( COMPUTING , isDebugLoadingStageEnabled() )
	serializeDebugExecutable( "jit" );
AVM_ENDIF_DEBUG_FLAG_AND( COMPUTING )

	if( mOutputSymbexScenariiEnabledGenerationFlag )
	{
		serializeScenarii();
	}

	if( mOutputSymbexGraphEnabledGenerationFlag )
	{
		serializeGraphizSymbexGraph();
	}

AVM_IF_DEBUG_FLAG_AND( COMPUTING , isDebugComputingStageEnabled() )

	serializeTextualSymbexGraph();

AVM_ENDIF_DEBUG_FLAG_AND( COMPUTING )


//	saveProjection();
//	saveProjectionScenarii(mParameterWObject);
}


/**
 * Serialization
 */
void Configuration::toStream(OutStream & out) const
{
	out << TAB << "configuration " << getNameID() << " {" << EOL

		<< TAB2 << "WorkspaceRootPath = " << VFS::WorkspaceRootPath << EOL

		<< TAB2 << "mProjectSourceLocation = "
		<< VFS::relativeWorkspacePath( mProjectSourceLocation )
		<< EOL
		<< TAB2 << "SpecificationFileLocation = "
		<< VFS::relativeWorkspacePath( mSpecificationFileLocation )
		<< EOL

		<< TAB2 << "isOwnedSpecificationFlag = "
		<< ( mOwnedSpecificationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "OutputFilenamePattern = "
		<< VFS::relativeWorkspacePath( mOutputFilenamePattern )
		<< EOL
		<< TAB2 << "DebugFilenamePattern  = "
		<< VFS::relativeWorkspacePath( mDebugFilenamePattern )
		<< EOL

		<< TAB2 << "isOutputExecutableEnabledGenerationFlag = "
		<< ( mOutputExecutableEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "OutputExecutableFileLocation = "
		<< VFS::relativeWorkspacePath( mOutputExecutableFileLocation )
		<< EOL

		<< TAB2 << "isOutputSymbexGraphEnabledGenerationFlag = "
		<< ( mOutputSymbexGraphEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "OutputSymbexGraphFileLocation = "
		<< VFS::relativeWorkspacePath( mOutputSymbexGraphFileLocation )
		<< EOL

		<< TAB2 << "isOutputSymbexScenariiEnabledGenerationFlag = "
		<< ( mOutputSymbexScenariiEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "OutputSymbexScenariiFileLocation = "
		<< VFS::relativeWorkspacePath( mOutputSymbexScenariiFileLocation )
		<< EOL

		<< TAB2 << "isDebugStageEnabled          = "
		<< ( mDebugStageEnabledFlag ? "true" : "false" ) << EOL

		<< TAB2 << "isDebugParsingStageEnabled   = "
		<< ( mDebugParsingStageEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "isDebugCompilingStageEnabled = "
		<< ( mDebugCompilingStageEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "isebugLoadingStageEnabled   = "
		<< ( mDebugLoadingStageEnabledGenerationFlag ? "true" : "false" )
		<< EOL

		<< TAB2 << "isDebugComputingEnabled     = "
		<< ( mDebugComputingStageEnabledGenerationFlag ? "true" : "false" )
		<< EOL
		<< TAB2 << "DebugOutputSymbexGraphTextFileLocation = "
		<< VFS::relativeWorkspacePath( mDebugOutputSymbexGraphTextFileLocation )
		<< EOL


		<< TAB2 << "mInconditionalStopMarkerLocation = "
		<< VFS::relativeWorkspacePath( mInconditionalStopMarkerLocation )
		<< EOL

		<< TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */
