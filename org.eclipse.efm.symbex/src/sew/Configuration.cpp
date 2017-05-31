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

#include <fam/serializer/GraphVizExecutionGraphSerializer.h>
#include <fam/serializer/GraphVizStatemachineSerializer.h>

#include <fml/executable/ExecutableSystem.h>

#include <fml/workflow/Query.h>

#include <sew/SymbexEngine.h>
#include <sew/Workflow.h>

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


/**
 * CONSTRUCTOR
 * Default
 */
Configuration::Configuration(SymbexEngine & aSymbexEngine, Workflow & aWorkflow)
: NamedElement( CLASS_KIND_T( Configuration ) , aSymbexEngine ),
mSymbexEngine( aSymbexEngine ),
mWorkflow( aWorkflow ),

mWObjectManager( WObject::FML_FQN_ROOT ),
mProjectSourceLocation( ),
mSpecificationFileLocation( ),

mOwnedSpecificationFlag( false ),

mOutputFilenamePattern( "output_%1%" ),
mDebugFilenamePattern ( "debug_%1%"  ),

mOutputExecutableEnabledGenerationFlag( false ),
mOutputExecutableFileLocation( ),

mOutputSymbexGraphEnabledGenerationFlag( false ),
mOutputSymbexGraphFileLocation( ),

mOutputSymbexScenariiEnabledGenerationFlag( false ),
mOutputSymbexScenariiFileLocation( ),

mDebugStageEnabledFlag( false ),
mDebugParsingStageEnabledFlag( false ),
mDebugCompilingStageEnabledFlag( false ),
mDebugLoadingStageEnabledFlag( false ),
mDebugComputingEnabledFlag( false ),

// Symbex Threading config
mMultitaskingFlag( false ),
mThreadCount( 1 ),

// Shell config
mInconditionalStopMarkerLocation( ),

mSpecification( NULL ),
mExecutableSystem( NULL ),

mTableOfRID( ),
mMainExecutionContext( ),
mInputContext( ),
mTrace( )
{
	//!! NOTHING
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
		avm_report(AVM_OS_LOG, "Configuration::destroy");

		if( mTrace.populated() )
		{
			ExecutionContext * itEC;
			while( mTrace.nonempty() )
			{
				mTrace.pop_last_to( itEC );
				mTrace.remove( itEC );
				sep::destroyElement( itEC );
			}
		}
		else if( mTrace.nonempty() )
		{
			sep::destroyElement( mTrace.pop_last() );
		}

		mMainExecutionContext.destroy();

		// Attention:> Necessaire pour briser des references circulaires !!!!
		destroyRIDRunningCode();

		mExecutableSystem.destroy();

		avm_report(AVM_OS_LOG, "~Configuration::destroy:> "
				"after destruction of executable & execution context");

		mSpecification.destroy();

		avm_report(AVM_OS_LOG, "~Configuration::destroy:> "
				"after destruction of specification");
	}
}

// Attention:> Necessaire pour briser des references circulaires !!!!
void Configuration::destroyRIDRunningCode()
{
	TableOfRuntimeID_T::iterator it = mTableOfRID.begin();
	TableOfRuntimeID_T::iterator itEnd = mTableOfRID.end();
	for( ; it != itEnd ; ++it )
	{
		(*it).finalize();
	}

//	mTableOfRID.clear();
}



/**
 * CONFIGURE
 */
/*
section project / SPECIFICATION
	src = <source-folder-path>

	file = "additional_file.xlia";

	main = "ascenseur.xlia";
endsection
*/
bool Configuration::configure(
		WObject * wfConfiguration, Configuration * prevConfiguration)
{
	WObject * aSECTION = Query::getWSequenceOrElse(
			wfConfiguration, "project", "SPECIFICATION");
	if( aSECTION != WObject::_NULL_ )
	{
		mProjectSourceLocation =
				Query::getWPropertyStringOrElse(aSECTION,
						"source", "src", VFS::WorkspaceSourcePath);

		mProjectSourceLocation = VFS::native_path(
				mProjectSourceLocation, VFS::WorkspaceRootPath);

		mSpecificationFileLocation =
				Query::getWPropertyStringOrElse(
						aSECTION, "model", "main", "");

		mOwnedSpecificationFlag = (mSpecificationFileLocation.size() > 0);

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

			if( VFS::checkReadingFile(mSpecificationFileLocation) )
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
	else if( prevConfiguration != NULL )
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
					(mOutputExecutableFileLocation.size() > 0);
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

			// Output SymbexGraph
			mOutputSymbexGraphFileLocation =
					Query::getRegexWPropertyString(aSECTION, "graph(viz)?", "");

			mOutputSymbexGraphEnabledGenerationFlag =
					(mOutputSymbexGraphFileLocation.size() > 0);
			if( mOutputSymbexGraphEnabledGenerationFlag )
			{
				mOutputSymbexGraphFileLocation = VFS::native_path(
					mOutputSymbexGraphFileLocation, VFS::WorkspaceOutputPath);
			}
			else
			{
				mOutputSymbexGraphFileLocation =
						mOutputFilenamePattern + SYMBEX_GRAPH_FILE_EXTENSION;
			}

			// Output Symbex Scenaii
			mOutputSymbexScenariiFileLocation =
					Query::getWPropertyString(aSECTION, "scenarii", "");

			mOutputSymbexScenariiEnabledGenerationFlag =
					(mOutputSymbexScenariiFileLocation.size() > 0);
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

		mDebugParsingStageEnabledFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "parsing");

		mDebugCompilingStageEnabledFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "executable");

		mDebugLoadingStageEnabledFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "loading");

		mDebugComputingEnabledFlag = mDebugStageEnabledFlag
				&& Query::hasWPropertyString(aSECTION, "execution");
	}

	bool isOK = configure_shell_symbex(wfConfiguration);

	return( isOK );
}


bool Configuration::configure_shell_symbex(WObject * wfConfiguration)
{
	// Symbex config
	WObject * configSYMBEX = Query::getRegexWSequence(
			wfConfiguration, Workflow::SECTION_SYMBEX_REGEX_ID);

	mMultitaskingFlag = Query::getWPropertyBoolean(
			configSYMBEX, "multitasking", mWorkflow.isMultitasking());

	mThreadCount = Query::getWPropertyInt(
			configSYMBEX, "thread", mWorkflow.getThreadCount());


	// Shell config
	WObject * configSHELL = Query::getRegexWSequence(
			wfConfiguration, Workflow::SECTION_SHELL_REGEX_ID);

	mInconditionalStopMarkerLocation =
			Query::getWPropertyString(configSHELL, "stop", "");
	if( mInconditionalStopMarkerLocation.empty() )
	{
		mInconditionalStopMarkerLocation =
				mWorkflow.getInconditionalStopMarkerLocation();
	}
	else
	{
		mInconditionalStopMarkerLocation =
				VFS::native_path(mInconditionalStopMarkerLocation);

		mInconditionalStopMarkerLocation = VFS::native_path(
				mInconditionalStopMarkerLocation, VFS::WorkspaceLogPath);
	}

	return( true );
}



bool Configuration::configureFormatter(WObject * FORMAT,
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
			isDebug, strID, SYMBEX_GRAPH_FILE_EXTENSION);
}



/**
 * Jose Projection
 */
//void Configuration::saveProjection(const std::string & strPrefixName)
//{
//	if( mOutputSymbexProjectionGraphEnabledGenerationFlag )
//	{
//		ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );
//
//		AVM_OS_LOG << _SEW_ << "Saving of projection (2)" << std::endl
//				<< TAB << "path: " << VFS::relativeWorkspacePath(
//				mOutputSymbexProjectionGraphFileLocation )
//				<< "... " << std::flush;
//
//		std::ofstream resultStream;
//		resultStream.open(mOutputSymbexProjectionGraphFileLocation.c_str(),
//				std::ios_base::out);
//		if( resultStream.good() )
//		{
//			OutStream os(resultStream, AVM_OUTPUT_INDENT);
//
//			ListOfExecutionContext::iterator it = getTrace().begin();
//			ListOfExecutionContext::iterator itEnd = getTrace().end();
//			for( ; it != itEnd ; ++it )
//			{
//				// Suppression de l'indentation dans le fichier de sortie
//				(*it)->toFscn(os, NULL);
//			}
//
//			resultStream.close();
//
//			AVM_OS_LOG << "OK" << std::endl ;
//		}
//		else
//		{
//			AVM_OS_LOG << std::endl << TAB
//					<< "    KO : Failed to open this file in write mode"
//					<< std::endl;
//		}
//	}
//}
//
//
//void Configuration::saveProjectionScenarii(const std::string & strPrefixName)
//{
//	if( mOutputSymbexProjectionScenariiEnabledGenerationFlag )
//	{
//		ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );
//
//		AVM_OS_LOG << _SEW_ << "Saving of projection FSCN " << std::endl
//				<< TAB << "path: " << VFS::relativeWorkspacePath(
//				mOutputSymbexProjectionScenariiFileLocation )
//				<< "... " << std::flush;
//
//		std::ofstream resultStream;
//		resultStream.open(mOutputSymbexProjectionScenariiFileLocation.c_str(),
//				std::ios_base::out);
//		if( resultStream.good() )
//		{
//			OutStream os(resultStream, AVM_OUTPUT_INDENT);
//
//			ListOfExecutionContext::iterator it = getTrace().begin();
//			ListOfExecutionContext::iterator itEnd = getTrace().end();
//			for( ; it != itEnd ; ++it )
//			{
//				// Suppression de l'indentation dans le fichier de sortie
//				(*it)->toFscn(os, NULL);
//			}
//
//			resultStream.close();
//
//			AVM_OS_LOG << "OK" << std::endl ;
//		}
//		else
//		{
//			AVM_OS_LOG << std::endl << TAB
//					<< "    KO : Failed to open this file in write mode"
//					<< std::endl;
//		}
//	}
//}
// end Jose Projection



///**
// * Configuration::saveSpecification
// *
// */
//void Configuration::saveSpecificationAfterCompilationStep(
//		const std::string & strPrefixName)
//{
//	MainDataConfiguration * aMDC = aMDC->getInstance();
//	ParameterManager * aPM = aMDC->getParameterManager();
//
//	std::string saveFileLocation =
//			aPM->getEngineDebugParsingLocation(strPrefixName);
//
//	if( aMDC->hasSpecification() && (not saveFileLocation.empty()) )
//	{
//		AVM_OS_LOG << _SEW_
//				<< "Saving of the internal specification "
//					"representation in textual format "
//				<< std::endl;
//
//		saveElementTextualView(aMDC->getSpecification(), saveFileLocation);
//	}
//}
//
//
///**
// * Configuration::saveExecutableSpecification
// *
// */
//void Configuration::saveExecutableSpecification(
//		const std::string & strPrefixName)
//{
//	MainDataConfiguration * aMDC = MainDataConfiguration::getInstance();
//	ParameterManager * aPM = aMDC->getParameterManager();
//
//	std::string saveFileLocation =
//			aPM->getEngineOutputExecutableLocation(strPrefixName);
//
//	if( not saveFileLocation.empty() )
//	{
//		AVM_OS_LOG << _SEW_ << "Saving of the compiled "
//				"specification representation in textual format "
//				<< std::endl;
//
//		saveFormTextualViews(aMDC->getExecutableSystem(), saveFileLocation);
//
//		saveFileLocation = aPM->getEngineOutputGraphLocation("fec_");
//		if( aMDC->hasMainExecutionContext() && (! saveFileLocation.empty()) )
//		{
//			saveElementTextualView(
//					aMDC->getMainExecutionContext(), saveFileLocation);
//		}
//	}
//}


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
	resultStream.open(saveFileLocation.c_str(), std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream os(resultStream);
		anElement.serialize(os);

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

void Configuration::serializeDebugExecutable(const std::string & strID)
{
	std::string saveFileLocation = formatFileLocation(
			true, strID, EXECUTABLE_FILE_EXTENSION);

	AVM_OS_CLOG << _DBG_
		<< "Saving of the Executable in text format --> "
		<< strID << std::endl;

	Configuration::saveElementTextualView(AVM_OS_LOG,
			mExecutableSystem, saveFileLocation);
}

void Configuration::serializeTextualExecutable()
{
	AVM_OS_LOG << _SEW_
			<< "Saving of the Executable in text format" << std::endl;

	Configuration::saveElementTextualView(AVM_OS_LOG,
			mExecutableSystem, mOutputExecutableFileLocation);
}


void Configuration::serializeGraphizExecutable()
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
	resultStream.open(saveFileLocation.c_str(), std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream os(resultStream, AVM_SPC_INDENT);

		GraphVizStatemachineSerializer::format(
			mSymbexEngine.getControllerUnitManager(), os, getSpecification());

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
void Configuration::serializeTextualSymbexGraph()
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the trace of the execution specification "
			"representation in textual format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath( mOutputSymbexGraphFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(mOutputSymbexGraphFileLocation.c_str(),
			std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream os(resultStream, AVM_SPC_INDENT);

		ListOfExecutionContext::const_iterator it = getTrace().begin();
		ListOfExecutionContext::const_iterator itEnd = getTrace().end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->serialize(os);
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
				true, "tec", SYMBEX_GRAPH_FILE_EXTENSION);

		saveElementTextualView(AVM_OS_LOG,
				getMainExecutionContext(), saveFileLocation);
	}
}

/**
 * serialize Graphiz SymbexGraph
 */
void Configuration::serializeGraphizSymbexGraph()
{
	std::string saveFileLocation = VFS::replace_extension(
			mOutputSymbexGraphFileLocation, GRAPHVIZ_FILE_EXTENSION);

	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the symbex trace of the execution specification "
			"representation in GraphViz format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath( saveFileLocation )
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(saveFileLocation.c_str(), std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream os(resultStream, AVM_SPC_INDENT);

		ListOfExecutionContext::const_iterator it = getTrace().begin();
		ListOfExecutionContext::const_iterator itEnd = getTrace().end();
		for( ; it != itEnd ; ++it )
		{
			GraphVizExecutionGraphSerializer::format(
				mSymbexEngine.getControllerUnitManager(), os, *(*it));
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


void Configuration::serializeScenarii()
{
	ScopeNewIndent scope( AVM_OS_LOG , AVM_TAB1_INDENT );

	AVM_OS_LOG << _SEW_
			<< "Saving of the trace of the execution specification "
			"representation in textual format " << std::endl;

	AVM_OS_LOG << TAB << "path: "
			<< VFS::relativeWorkspacePath(mOutputSymbexScenariiFileLocation)
			<< "... " << std::flush;

	std::ofstream resultStream;
	resultStream.open(mOutputSymbexScenariiFileLocation.c_str(),
			std::ios_base::out);
	if( resultStream.good() )
	{
		OutStream os(resultStream, AVM_FSCN_INDENT);

		ListOfExecutionContext::const_iterator it = getTrace().begin();
		ListOfExecutionContext::const_iterator itEnd = getTrace().end();
		for( ; it != itEnd ; ++it )
		{
			(*it)->toFscn(os, NULL);
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
void Configuration::serializeBuildingResult()
{
	if( mOutputExecutableEnabledGenerationFlag )
	{
		serializeTextualExecutable();

		serializeGraphizExecutable();
	}
}

/**
 * Serialization computing stage
 */
void Configuration::serializeComputingResult()
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
AVM_IF_DEBUG_ENABLED

		serializeTextualSymbexGraph();

AVM_ENDIF_DEBUG_ENABLED

		serializeGraphizSymbexGraph();
	}

//	saveProjection();
//	saveProjectionScenarii(mParameterWObject);
}


/**
 * Serialization
 */
void Configuration::toStream(OutStream & os) const
{
	os << TAB << "configuration " << getNameID() << " {" << EOL;

	os << TAB2 << "WorkspaceRootPath = " << VFS::WorkspaceRootPath << EOL;

	os << TAB2 << "mProjectSourceLocation = "
			<< VFS::relativeWorkspacePath( mProjectSourceLocation )
			<< EOL;
	os << TAB2 << "mSpecificationFileLocation = "
			<< VFS::relativeWorkspacePath( mSpecificationFileLocation )
			<< EOL;

	os << TAB2 << "mOwnedSpecificationFlag = "
			<< ( mOwnedSpecificationFlag ? "true" : "false" )
			<< EOL;
	os << TAB2 << "mOutputFilenamePattern = "
			<< VFS::relativeWorkspacePath( mOutputFilenamePattern )
			<< EOL;
	os << TAB2 << "mDebugFilenamePattern  = "
			<< VFS::relativeWorkspacePath( mDebugFilenamePattern )
			<< EOL;

	os << TAB2 << "mOutputExecutableEnabledGenerationFlag = "
			<< ( mOutputExecutableEnabledGenerationFlag ? "true" : "false" )
			<< EOL;
	os << TAB2 << "mOutputExecutableFileLocation = "
			<< VFS::relativeWorkspacePath( mOutputExecutableFileLocation )
			<< EOL;

	os << TAB2 << "mOutputSymbexGraphEnabledGenerationFlag = "
			<< ( mOutputSymbexGraphEnabledGenerationFlag ? "true" : "false" )
			<< EOL;
	os << TAB2 << "mOutputSymbexGraphFileLocation = "
			<< VFS::relativeWorkspacePath( mOutputSymbexGraphFileLocation )
			<< EOL;

	os << TAB2 << "mOutputSymbexScenariiEnabledGenerationFlag = "
			<< ( mOutputSymbexScenariiEnabledGenerationFlag ? "true" : "false" )
			<< EOL;
	os << TAB2 << "mOutputSymbexScenariiFileLocation = "
			<< VFS::relativeWorkspacePath( mOutputSymbexScenariiFileLocation )
			<< EOL;

	os << TAB2 << "mDebugStageEnabledFlag          = "
			<< ( mDebugStageEnabledFlag ? "true" : "false" ) << EOL;

	os << TAB2 << "mDebugParsingStageEnabledFlag   = "
			<< ( mDebugParsingStageEnabledFlag ? "true" : "false" ) << EOL;

	os << TAB2 << "mDebugCompilingStageEnabledFlag = "
			<< ( mDebugCompilingStageEnabledFlag ? "true" : "false" ) << EOL;

	os << TAB2 << "mDebugLoadingStageEnabledFlag   = "
			<< ( mDebugLoadingStageEnabledFlag ? "true" : "false" ) << EOL;

	os << TAB2 << "mDebugComputingEnabledFlag      = "
			<< ( mDebugComputingEnabledFlag ? "true" : "false" ) << EOL;


	os << TAB2 << "mInconditionalStopMarkerLocation = "
			<< VFS::relativeWorkspacePath( mInconditionalStopMarkerLocation )
			<< EOL;

	os << TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */
