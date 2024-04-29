/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 4 févr. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmTraceDirector.h"

#include <algorithm>
#include <fstream>

#include <util/avm_string.h>
#include <util/avm_vfs.h>

#include <collection/Typedef.h>

#include <fml/template/TimedMachine.h>

#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/expression/ExpressionConstructor.h>

#include <fml/type/TypeSpecifier.h>

#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TracePoint.h>

#include <fml/type/TypeManager.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <famcore/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/SymbexControllerUnitManager.h>


namespace sep
{

/**
 * GETTER - SETTER
 * APPEND -- SAVE
 * POP_FRONT
 * SIZE
 */
void AvmTraceDirective::setCoverage(std::size_t & offset, std::size_t count)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_LOG << "AvmTraceDirective::setCoverage< offset: " << offset
			<< " , count: " << count << " >" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	mRequiredPointFlags[ offset ] = true;

	offset = offset + count;
}

void AvmTraceDirective::setGoalAchieved(AvmTraceDirector & aTraceDirector)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_LOG << "AvmTraceDirective::setGoalAchieved:> " << std::endl;
	traceMinimum(AVM_OS_LOG);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	mStatus = AvmTraceDirective::COVERED;

	if( aTraceDirector.isFoldingFlag() &&
		aTraceDirector.isNormalizationFlag() )
	{
		normalize( aTraceDirector );
	}

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_LOG << "AvmTraceDirective::setGoalAchieved:> normalize !" << std::endl;
	traceMinimum(AVM_OS_LOG);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
}


void AvmTraceDirective::normalize(AvmTraceDirector & aTraceDirector)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_LOG << "AvmTraceDirective::normalize:> folding trace ..." << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

	std::string lineBuffer = VFS::relativeProjectPath(mTraceLocation,
			aTraceDirector.getFolder().location + VFS::PathSeparator);

	if( points.populated() && mRequiredPointFlags.anyFalse() )
	{
		std::ofstream resultStream;

		lineBuffer = VFS::prefixFilename(lineBuffer, "diversity_");

		if( not VFS::checkWritingFileFolder( lineBuffer ) )
		{
			AVM_OS_WARN << "normalize:> Failed to open trace file << "
					<< lineBuffer << " >> !!!" << std::endl;

			return;
		}

		resultStream.open(lineBuffer, std::ios_base::out);
		if( not resultStream.good() )
		{
			AVM_OS_WARN << "normalize:> Failed to open trace file << "
					<< lineBuffer << " >> !!!" << std::endl;

			return;
		}

		OutStream save_os(resultStream, AVM_NO_INDENT);

		std::ifstream aTraceStream( mTraceLocation );

		std::size_t offset = 0;
		for( ; aTraceStream.good() ; ++offset )
		{
			std::getline(aTraceStream, lineBuffer);

			save_os << lineBuffer << std::endl;

			if( offset >= 4 )
			{
				break;
			}
		}


		BFList::iterator it = points.begin();
		BFList::iterator endIt = points.end();

		TracePoint * timeTP = nullptr;

		timeTP = (*it).to< TracePoint >().val(
				mTimePointOffset).to_ptr< TracePoint >();

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	timeTP->toStream( AVM_OS_LOG << "time point:> " );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

		avm_float_t timeDiff;
		avm_float_t timeTotal = 0;

		avm_float_t currTime;
		avm_float_t prevTime = timeTP->value.toFloat();

		std::string::size_type pos;

		for( offset = 1 , ++it ; it != endIt ; ++offset )
		{
			if( aTraceStream.good() )
			{
				std::getline(aTraceStream, lineBuffer);
			}
			else
			{
				AVM_OS_LOG << "normalize:> Failed to read trace file << "
						<< mTraceLocation << " >> !!!" << std::endl;

				break;
			}

			timeTP = (*it).to< TracePoint >().val(
					mTimePointOffset).to_ptr< TracePoint >();

			currTime = timeTP->value.toFloat();
			timeDiff = currTime - prevTime;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	timeTP->toStream( AVM_OS_LOG << "time point:> " );
	AVM_OS_LOG << "time diff < prev: " << prevTime
			<< " , curr: " << currTime << " > diff: " << timeDiff << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

			prevTime = currTime;

			if( mRequiredPointFlags.empty() || mRequiredPointFlags[offset] )
			{
				timeTotal = timeTotal + timeDiff;
				timeTP->value = ExpressionConstructor::newFloat( timeTotal );

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	(*it).to< TracePoint >().toStream(AVM_OS_LOG << "update Point:> ");
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				++it;

				pos = lineBuffer.find(';');
				save_os << lineBuffer.substr(0, pos + 1)
						<< OS_FLOAT_PRECISION << timeTotal
						<< lineBuffer.substr( lineBuffer.find(';', pos + 1) )
						<< std::endl;
			}
			else
			{
				mRequiredPointFlags[offset] = true;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	AVM_OS_LOG << "AvmTraceDirective::setGoalAchieved:> remove: "
			<< IGNORE_FIRST_TAB;
	(*it).to< TracePoint >().toStream(AVM_OS_LOG);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				it = points.erase( it );
			}
		}

		mRequiredPointFlags.resize( points.size() );

		mReducedFlag = true;

		resultStream.close();
	}
	else
	{
		if( VFS::checkWritingFileFolder( lineBuffer ) )
		{
			VFS::copyTo(mTraceLocation, lineBuffer);
		}
		else
		{
			AVM_OS_WARN << "normalize:> Failed to open trace file << "
					<< lineBuffer << " >> !!!" << std::endl;

			return;
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceDirective::toStream(OutStream & os) const
{
	os << TAB << "trace#" << tid << "<" << strStatus()
			<< ", size:" << points.size();
	if( mEC != nullptr )
	{
		os << ", ctx:" << mEC->getIdNumber();
	}
	if( not mTraceID.empty() )
	{
		os << ", utid:" << mTraceID;
	}
	if( not mTraceLocation.empty() )
	{
		os << ", file:" << VFS::relativeProjectPath(mTraceLocation);
	}
	os << "> { " << combinator->strOp() << EOL_INCR_INDENT;

	BFList::const_iterator it = points.begin();
	BFList::const_iterator endIt = points.end();
	for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
	{
		os << TAB << ( ( (not mRequiredPointFlags.empty()) &&
							mRequiredPointFlags[offset] )? "[+]" : "[-]" )
				<< IGNORE_FIRST_TAB;

		(*it).toStream(os);
	}

	os << TAB << "}" << EOL_FLUSH;
}


void AvmTraceDirective::traceAbstract(OutStream & os) const
{
	os << TAB << mTraceLabel << FQN_ID_ROOT_SEPARATOR
			<< VFS::relativeProjectPath(mTraceLocation)
			<< EOL_INCR_INDENT;

	points.front().to< TracePoint >().toStream(os);

	os << TAB << " ==> ";

	points.back().to< TracePoint >().toStream(os);

	os << EOL_FLUSH_DECR_INDENT;
}


void AvmTraceDirective::traceMinimum(OutStream & os) const
{
	os << TAB << "trace#" << tid << "<" << strStatus()
					<< ", size:" << points.size();
	if( mEC != nullptr )
	{
		os << ", ctx:" << mEC->getIdNumber();
	}
	if( not mTraceID.empty() )
	{
		os << ", utid:" << mTraceID;
	}
	if( not mTraceLocation.empty() )
	{
		os << ", " << mTraceLabel << ":"
				<< VFS::relativeProjectPath(mTraceLocation);
	}

	os << "> { " << combinator->strOp() << EOL_INCR_INDENT;

	BFList::const_iterator it = points.begin();
	BFList::const_iterator endIt = points.end();
	for( std::size_t offset = 0 ; it != endIt ; ++it , ++offset )
	{
		os << TAB << ( ( (not mRequiredPointFlags.empty()) &&
							mRequiredPointFlags[offset] ) ? "[+]" : "[-]" )
				<< IGNORE_FIRST_TAB;

		if( (*it).is< TracePoint >() )
		{
			(*it).to< TracePoint >().toStream(os);
		}
		else if( (*it).is< TraceSequence >() )
		{
			(*it).to< TraceSequence >().toStream(os);
		}
		else
		{
			os << (*it);
		}
	}

	os << DECR_INDENT_TAB << "}" << EOL_FLUSH;
}



/**
 * PROCESSOR FACTORY
 * for automatic registration in the processor repository
 */
//AVM_IMPLEMENT_AUTO_REGISTERED_PROCESSOR_FACTORY_CLASS( AvmTraceDirector )


/*
prototype process::trace_director as &avm::processor.TRACE_DIRECTOR is
 section PROPERTY
  @schema = "format/TestCase.schema";
  @trace  = "format/TestCaseSample.trace";
 endsection PROPERTY
endprototype
*/


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDirector::configureImpl()
{
	// SUPER CONFIGURATION
	mConfigFlag = BaseCoverageFilter::configureImpl();


	const WObject * thePROPERTY = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("property", "PROPERTY"), getParameterWObject());
	if( thePROPERTY != WObject::_NULL_ )
	{
		mConsecutiveFlag = Query::getWPropertyBoolean(
				thePROPERTY, "consecutive", true);

		mDeterminismFlag = Query::getWPropertyBoolean(
				thePROPERTY, "determinism", true);

		mFoldingFlag = Query::getWPropertyBoolean(
				thePROPERTY, "folding", true);

		/**
		 * SCHEMA File
		 * global context
		 */
		mSchemaFileLocation = Query::getWPropertyString(
				thePROPERTY, "schema", "");

		mSchemaFileLocation = VFS::native_path(
				mSchemaFileLocation, VFS::ProjectSourcePath);

		mConfigFlag = VFS::checkReadingFile(mSchemaFileLocation)
				&& mConfigFlag;

		mParsedFileCount = Query::getRegexWPropertyPosSizeT(
				thePROPERTY, CONS_WID2("file", "count"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mSortedFileFlag = Query::getRegexWPropertyBoolean(
				thePROPERTY, CONS_WID2("file", "sort"), false);
	}
	else
	{
		mConfigFlag = false;
	}


	const WObject * theTRACE = Query::getRegexWSequence(getParameterWObject(),
			OR_WID2("trace", "TRACE"), thePROPERTY);
	if( theTRACE != WObject::_NULL_ )
	{
		/**
		 * SCHEMA File
		 * local context
		 */
		std::string localSchemaFileLocation = Query::getWPropertyString(
				theTRACE, "schema", mSchemaFileLocation);
		if( localSchemaFileLocation != mSchemaFileLocation )
		{
			localSchemaFileLocation = VFS::native_path(
					localSchemaFileLocation, VFS::ProjectSourcePath);
			if( VFS::checkReadingFile(localSchemaFileLocation) )
			{
				mSchemaFileLocation = localSchemaFileLocation;
			}
		}

		/**
		 * TRACE Files & folder
		 */
		std::string aLabel;
		std::string aLocation;

		WObject::const_iterator itWfO = theTRACE->owned_begin();
		WObject::const_iterator endWfO = theTRACE->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				aLabel = (*itWfO)->getNameID();
				if( StringTools::startsWith(aLabel, "file") )
				{
					aLocation = VFS::native_path(
							(*itWfO)->toStringValue(),
							VFS::ProjectSourcePath);

					if( VFS::checkReadingFile(aLocation) )
					{
						mTableOfTraceFileLocation.append( aLocation );
						mTableOfTraceLabel.append( aLabel );
					}
					else
					{
						AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
								<< getParameterWObject()->getFullyQualifiedNameID()
								<< " >> " << std::endl
								<< (*itWfO)->errorLocation()
								<< "Unfound trace file << " << aLocation
								<< " >> !!!" << std::endl;
					}
				}
				else if( StringTools::startsWith(aLabel, "folder") ||
						StringTools::startsWith(aLabel, "directory") )
				{
					aLocation = VFS::native_path(
							(*itWfO)->toStringValue(), VFS::ProjectSourcePath);

					mFileOffset = mTableOfTraceFileLocation.size();
					if( VFS::listAllFiles(aLocation,
							mTableOfTraceFileLocation, true) )
					{
						// sorting files from folder
						if( mSortedFileFlag )
						{
							std::sort(mTableOfTraceFileLocation.begin() +
								mFileOffset, mTableOfTraceFileLocation.end());
						}

						mFileCount = mTableOfTraceFileLocation.size();
						mTraceOffset = 0;
						for( ; mFileOffset < mFileCount ; ++mFileOffset )
						{
							mTableOfTraceLabel.append( OSS()
									<< aLabel << "#file#" << (++mTraceOffset) );
						}
					}
					else
					{
						AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
								<< getParameterWObject()->getFullyQualifiedNameID()
								<< " >> " << std::endl
								<< (*itWfO)->errorLocation()
								<< "Unfound trace folder << " << aLocation
								<< " >> !!!" << std::endl;
					}
				}
			}
		}

		mFileCount = mTableOfTraceFileLocation.size();
		if( mFileCount == 0 )
		{
			mConfigFlag = false;

			AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
					<< getParameterWObject()->getFullyQualifiedNameID()
					<< " >> " << std::endl
					<< theTRACE->errorLocation()
					<< "Zero trace file found !!!" << std::endl;
		}
	}
	else
	{
		mConfigFlag = false;
	}

	if( mConfigFlag )
	{
		/**
		 * SCHEMA Analysis
		 * parsing file & configuration
		 */
		AVM_OS_LOG << std::endl << EMPHASIS("Parsing Schema ...", '*', 100);

		if( parseSchema() )
		{
			mTableOfTypeSpecifier.toStream(AVM_OS_LOG);

			mTraceVariables.toStream(AVM_OS_LOG);

			mSpecVariables.toStream(AVM_OS_LOG);

			if( mTraceVariables.size() != mSpecVariables.size() )
			{
				mConfigFlag = false;

				AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
						<< getParameterWObject()->getFullyQualifiedNameID()
						<< " >> " << std::endl
						<< Query::getWProperty(thePROPERTY, "schema")->errorLocation()
						<< "Schema file analysis failed < binding size error > !!!"
						<< std::endl
						<< "\tSchema file : " << mSchemaFileLocation << std::endl;
			}
		}
		else
		{
			mConfigFlag = false;

			mTableOfTypeSpecifier.toStream(AVM_OS_CERR);

			mTraceVariables.toStream(AVM_OS_CERR);

			mSpecVariables.toStream(AVM_OS_CERR);

			AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
					<< getParameterWObject()->getFullyQualifiedNameID()
					<< " >> " << std::endl
					<< Query::getWProperty(thePROPERTY, "schema")->errorLocation()
					<< "Schema file analysis failed !!!" << std::endl
					<< "\tSchema file : " << mSchemaFileLocation << std::endl;
		}

		AVM_OS_LOG << std::endl
				<< EMPHASIS("End Parse Schema", '*', 100);
	}

	if( mConfigFlag )
	{
		mCoverageStatistics.mNumberOfElements =
				std::min(mFileCount, mParsedFileCount);

		mCoverageStatistics.mCoverageBitset.resize(
				mCoverageStatistics.mNumberOfElements, false);

		mConfigFlag = getExecutionQueue().reconfigure(
				ExecutionQueue::STRATEGY_WEIGHT_ALL_BFS);
	}

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmTraceDirector::reportDefault(OutStream & os) const
{
	os << TAB1 << "TRACE DIRECTOR" << EOL;

	os << TAB2 << "Coverage "
			<< mCoverageStatistics.strCoverageRate() << " ==> "
			<< (mCoverageStatistics.goalAchieved() ? "DONE !" : "FAILED !")
			<< EOL;

	os << TAB2 << "Redundancy Count : " << mRedundancyCount << EOL_FLUSH;
}


void AvmTraceDirector::reportMaximum(OutStream & os) const
{
	os << TAB1 << "TRACE DIRECTOR[ slice: " << mSliceCount
			<< " ] Coverage: " << mCoverageStatistics.strCoverageRate()
			<< " ==> "
			<< (mCoverageStatistics.goalAchieved() ? "DONE !" : "FAILED !")
			<< std::endl;

	os << TAB2 << "Redundancy Count : " << mRedundancyCount << EOL;

	os << TAB2 << "Redundancy List  : " << EOL;

	BFList::const_raw_iterator< GenericInfoData > itInfo;
	BFList::const_raw_iterator< GenericInfoData > endInfo;
	AvmTraceDirective * infoTrace = nullptr;

	BFVector::const_raw_iterator< AvmTraceDirective >
	itTrace = mTableOfRedundantTrace.begin();
	BFVector::const_raw_iterator< AvmTraceDirective >
	endTrace = mTableOfRedundantTrace.end();
	for( ; itTrace < endTrace ; ++itTrace )
	{
		switch( (itTrace)->mStatus )
		{
			case AvmTraceDirective::REDUNDANT:
			{
				os << TAB3 << "<" << (itTrace)->strStatus() << "> "
						<< (itTrace)->strInfo() << EOL;

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
				ListOfExecutionContext::const_iterator
				ecQueueIt = (itTrace)->mRedundantEC.begin();
				ListOfExecutionContext::const_iterator
				ecQueueItEnd = (itTrace)->mRedundantEC.end();
				for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
				{
					if( (*ecQueueIt)->hasInfo() )
					{
						itInfo = (*ecQueueIt)->getInfos().begin();
						endInfo = (*ecQueueIt)->getInfos().end();
						for( ; itInfo != endInfo ; ++itInfo )
						{
							if( itInfo->isInfo(*this) &&
								itInfo->getData().is< AvmTraceDirective >() )
							{
								infoTrace = itInfo->getData().
										to_ptr< AvmTraceDirective >();

								if( infoTrace != (itTrace) )
								{
									os << TAB3  << "==> " << AVM_NO_INDENT;
									(*ecQueueIt)->traceMinimum(os);
									os << END_INDENT << " |= "
											<< infoTrace->strInfo() << EOL;

									if( mMinimizationFlag )
									{
										break;
									}
								}
							}
						}
					}
				}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				break;
			}

			case AvmTraceDirective::ABORTED:
			case AvmTraceDirective::UNKNOWN:
			case AvmTraceDirective::UNDEFINED:
			{
				os << TAB3 << "<" << (itTrace)->strStatus() << "> "
						<< (itTrace)->strInfo() << EOL;

				break;
			}

			default:
			{
				break;
			}
		}
	}

	os << TAB1 << "TRACE DIRECTOR[ slice: " << mSliceCount
			<< " ] Coverage: " << mCoverageStatistics.strCoverageRate()
			<< " ==> "
			<< (mCoverageStatistics.goalAchieved() ? "DONE !" : "FAILED !")
			<< std::endl;

	os << TAB2 << "Redundancy Count : " << mRedundancyCount << EOL_FLUSH;
}



void AvmTraceDirector::reportTrace(OutStream & os) const
{
	os << TAB1 << "Nom du cas de test;Longueur;Unicity ID"
			<< EOL2_TAB
			<< "Coverage of "   << mCoverageStatistics.mNumberOfElements
			<< " test case / Non Redundant;"
			<< mCoverageStatistics.mNumberOfCovered
			<< ";" << (mCoverageStatistics.mNumberOfCovered - mRedundancyCount)
			<< EOL2;


	BFList::const_raw_iterator< GenericInfoData > itInfo;
	BFList::const_raw_iterator< GenericInfoData > endInfo;
	AvmTraceDirective * infoTrace = nullptr;
	bool isnotReported = false;

	BFVector::const_raw_iterator< AvmTraceDirective >
	itTrace = mTableOfAnalyzedTrace.begin();
	BFVector::const_raw_iterator< AvmTraceDirective >
	endTrace = mTableOfAnalyzedTrace.end();
	for( ; itTrace < endTrace ; ++itTrace )
	{
		os << (itTrace)->mTraceID << " : " //<< (itTrace)->tid << " : "
				<< VFS::filename( (itTrace)->mTraceLocation ) << ";"
				<< ( ((itTrace)->mEC != nullptr) ?
						(itTrace)->mEC->getHeight() : 0 )
				<< ";";

		switch( (itTrace)->mStatus )
		{
			case AvmTraceDirective::COVERED:
			{
				os << (itTrace)->tid;

				break;
			}

			case AvmTraceDirective::REDUNDANT:
			{
				if( (itTrace)->mRedundantTrace != nullptr )
				{
					infoTrace = (itTrace)->mRedundantTrace;
					while( infoTrace->mRedundantTrace != nullptr )
					{
						infoTrace = infoTrace->mRedundantTrace;
					}
					// Optimisation
					(itTrace)->mRedundantTrace = infoTrace;

					os << infoTrace->tid;
				}
				else
				{
					os << "mRedundantTrace == nullptr";
				}
				break;

				isnotReported = true ;

				if( ((itTrace)->mEC != nullptr) && (itTrace)->mEC->hasInfo() )
				{
					itInfo = (itTrace)->mEC->getInfos().begin();
					endInfo = (itTrace)->mEC->getInfos().end();
					for( ; isnotReported && (itInfo != endInfo) ; ++itInfo )
					{
						if( itInfo->isInfo(*this) &&
							itInfo->getData().is< AvmTraceDirective >() )
						{
							infoTrace = itInfo->getData().
									to_ptr< AvmTraceDirective >();

							if( infoTrace != (itTrace) )
							{
								os << infoTrace->tid;

								isnotReported = false;
								break;
							}
						}
					}

					if( not isnotReported )
					{
						break;
					}
				}

				ListOfExecutionContext::const_iterator
				ecQueueIt = (itTrace)->mRedundantEC.begin();
				ListOfExecutionContext::const_iterator
				ecQueueItEnd = (itTrace)->mRedundantEC.end();
				for( ; isnotReported && (ecQueueIt != ecQueueItEnd) ; ++ecQueueIt )
				{
					if( (*ecQueueIt)->hasInfo() )
					{
						itInfo = (*ecQueueIt)->getInfos().begin();
						endInfo = (*ecQueueIt)->getInfos().end();
						for( ; isnotReported && (itInfo != endInfo) ; ++itInfo )
						{
							if( itInfo->isInfo(*this) &&
								itInfo->getData().is< AvmTraceDirective >() )
							{
								infoTrace = itInfo->getData().
										to_ptr< AvmTraceDirective >();

								if( infoTrace != (itTrace) )
								{
									os << infoTrace->tid;

									isnotReported = false;
									break;
								}
							}
						}
					}
				}

				if( isnotReported )
				{
					os << (itTrace)->strStatus();
				}

				break;
			}

			case AvmTraceDirective::ABORTED:
			case AvmTraceDirective::PENDING:
			case AvmTraceDirective::UNKNOWN:
			case AvmTraceDirective::UNDEFINED:
			{
				os << (itTrace)->strStatus();

				break;
			}

			default:
			{
				os << 0;

				break;
			}
		}

		os << EOL_FLUSH;
	}
}


////////////////////////////////////////////////////////////////////////////////
// PARSER TOOLS
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDirector::nextLine(std::ifstream & aStream)
{
	while( aStream.good() )
	{
		std::getline(aStream, mParseLine);

		StringTools::ltrim( mParseLine );

		if( mParseLine.empty() || mParseLine[0] == '#' )
		{
			//!! NOTHING
		}
		else
		{
			return( true );
		}
	}

	mEndOfFile = true;

	return( false );
}

bool AvmTraceDirector::nextToken(std::ifstream & aStream)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	return( StringTools::nextToken(mParseLine, mParseToken) );
}

bool AvmTraceDirector::nextToken(std::ifstream & aStream,
		const std::string & separator)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	return( StringTools::nextToken(mParseLine, mParseToken, separator) );
}


unsigned int AvmTraceDirector::nextTokenNewLine(std::ifstream & aStream)
{
	unsigned int count = 0;

	for( ; (not mEndOfFile) ; ++count )
	{
		if( mParseLine.empty() )
		{
			if( aStream.good() )
			{
				std::getline(aStream, mParseLine);
			}
			else
			{
				mEndOfFile = true;

				break;
			}
		}

		if( mParseLine.empty() )
		{
			// continue
		}
		else if( (mParseLine[0] == '\n') || (mParseLine[0] == '\r') )
		{
			StringTools::ltrim(mParseLine);
		}
		else
		{
			StringTools::ltrim(mParseLine);

			if( mParseLine.empty() )
			{
				// continue
			}
			else if( (mParseLine[0] == '#') )
			{
				mParseLine.clear();
			}
			else
			{
				break;
			}
		}
	}

	return( count );
}

bool AvmTraceDirector::nextTokenChar(
		std::ifstream & aStream, char expectedChar)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	if( mParseLine[0] == expectedChar )
	{
		mParseToken = mParseLine[0];

		StringTools::ltrim(mParseLine, 1);

		return( true );
	}

	return( false );
}

char AvmTraceDirector::nextTokenChar(
		std::ifstream & aStream, const std::string & expectedChars)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	std::string::size_type pos = expectedChars.find(mParseLine[0]);

	if( pos != std::string::npos )
	{
		mParseToken = mParseLine[0];

		StringTools::ltrim(mParseLine, 1);

		return( mParseToken[0] );
	}

	return( static_cast< char >( 0 ) );
}


bool AvmTraceDirector::nextTokenWord(
		std::ifstream & aStream, const std::string & expectedWord)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	return( StringTools::nextTokenWord(mParseLine, mParseToken, expectedWord) );
}


bool AvmTraceDirector::nextTokenID(std::ifstream & aStream)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	return( StringTools::nextTokenID(mParseLine, mParseToken) );
}

bool AvmTraceDirector::nextTokenUFID(std::ifstream & aStream)
{
	if( mParseLine.empty() )
	{
		if( not nextLine(aStream) )
		{
			return( false );
		}
	}

	return( StringTools::nextTokenUFID(mParseLine, mParseToken) );
}


bool AvmTraceDirector::nextTokenAfter(
		std::ifstream & aStream, char expectedChar)
{
	if( nextToken(aStream) )
	{
		if( mParseToken[0] == expectedChar )
		{
			if( mParseToken.size() == 1 )
			{
				return( nextToken(aStream) );
			}
			else
			{
				mParseToken = mParseToken.substr(1);

				return( true );
			}
		}

	}

	return( false );
}

bool AvmTraceDirector::nextTokenAfter(
		std::ifstream & aStream, const std::string & expectedWord)
{
	if( nextToken(aStream) )
	{
		if( mParseToken == expectedWord )
		{
			return( nextToken(aStream) );
		}
	}

	return( false );
}


/**
 * SCHEMA
 */
bool AvmTraceDirector::parseSchema()
{
	mEndOfFile = false;

	std::ifstream aSchemaStream( mSchemaFileLocation );

	bool isParseOK = aSchemaStream.good();

	while( isParseOK )
	{
		if( nextTokenWord(aSchemaStream, "type") )
		{
			isParseOK = parseSchemaDataType(aSchemaStream);
		}
		else if( nextTokenWord(aSchemaStream, "trace") )
		{
			isParseOK = parseSchemaTracedef(aSchemaStream);
		}
		else if( nextTokenWord(aSchemaStream, "spec") )
		{
			isParseOK = parseSchemaSpecBind(aSchemaStream);
		}
		else if( mEndOfFile )
		{
			break;
		}
		else
		{
			isParseOK = false;
		}
	}

	aSchemaStream.close();

	return( isParseOK );
}


bool AvmTraceDirector::parseSchemaDataType(std::ifstream & aSchemaStream)
{
//	AVM_OS_COUT << TAB2 << "type:> " << mParseLine << std::endl;
	if( nextTokenID(aSchemaStream) )
	{
		std::string typeID = mParseToken;

//		AVM_OS_COUT << TAB2 << "ID:>" << typeID << "<:" << std::endl;
		if( nextTokenWord(aSchemaStream, "enum") )
		{
			if( nextTokenChar(aSchemaStream, '{') )
			{
				return( parseSchemaDataTypeEnum(aSchemaStream, typeID) );
			}
		}
	}

	return( false );
}

bool AvmTraceDirector::parseSchemaDataTypeEnum(
		std::ifstream & aSchemaStream, const std::string & typeID)
{
	TypeSpecifier enumT( TypeManager::newEnum(typeID) );
	mTableOfTypeSpecifier.append(enumT);

	InstanceOfData * anInstanceSymbol;

	Modifier aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER;

	for( avm_offset_t anOffset = 0 ; nextTokenID(aSchemaStream) ; ++anOffset )
	{
//		AVM_OS_COUT << TAB2 << "SYMBOL>" << mParseToken << "<:" << std::endl;

		anInstanceSymbol = new InstanceOfData(
				IPointerVariableNature::POINTER_ENUM_SYMBOL_NATURE,
				nullptr, Variable::nullref(), enumT.enumT(), anOffset, aModifier);
		anInstanceSymbol->setAllNameID(mParseToken, mParseToken);

		enumT.saveSymbol( anInstanceSymbol );

		switch( nextTokenChar(aSchemaStream, ",}") )
		{
			case ',':
			{
				break;
			}
			case '}':
			{
				return( true );
			}
			default:
			{
				return( false );
			}
		}
	}

	return( false );
}


bool AvmTraceDirector::parseSchemaTracedef(std::ifstream & aSchemaStream)
{
	if( nextTokenChar(aSchemaStream, '{') )
	{
		InstanceOfData * aVariable;
		TypeSpecifier attrT;
		Modifier aModifier = Modifier::PROPERTY_UNDEFINED_MODIFIER;

		for( avm_offset_t anOffset = 0 ; (not mEndOfFile) ; ++anOffset )
		{
			switch( nextTokenChar(aSchemaStream, "+*-}") )
			{
				case '+':
				{
					aModifier.setVisibilityPublic();
					break;
				}
				case '*':
				{
					aModifier.setVisibilityProtected();
					break;
				}
				case '-':
				{
					aModifier.setVisibilityPrivate();
					break;
				}
				default:
				{
					aModifier.unsetVisibilityKind();
					break;
				}
			}

			if( nextTokenWord(aSchemaStream, "var") )
			{
//				AVM_OS_COUT << TAB2 << "var:> " << mParseLine << std::endl;
			}
			else
			{
				AVM_OS_WARN << "parseSchemaTracedef:> "
						"Expected token << var >> found << "
						<< mParseToken << " >> before << "
						<< mParseLine << " >> !!!" << std::endl;

				return( false );
			}

			if( nextTokenID(aSchemaStream) )
			{
				attrT = mTableOfTypeSpecifier.getByNameID(mParseToken);

				if( attrT.invalid() )
				{
					attrT = TypeManager::getPrimitiveType(mParseToken);
					if( attrT.invalid() )
					{
						AVM_OS_WARN << "parseSchemaTracedef:> Unfound type << "
								<< mParseToken << " >> before << "
								<< mParseLine << " >> !!!" << std::endl;

						attrT = TypeManager::UNIVERSAL;
					}
				}
			}
			else
			{
				return( false );
			}

			if( nextTokenID(aSchemaStream) )
			{
				aVariable = new InstanceOfData(
						IPointerVariableNature::POINTER_STANDARD_NATURE,
						nullptr, Variable::nullref(), attrT.classT(),
						anOffset, aModifier);
				aVariable->setAllNameID(mParseToken, mParseToken);

				mTraceVariables.save(aVariable);
			}
			else
			{
				return( false );
			}

			switch( nextTokenChar(aSchemaStream, ";}") )
			{
				case ';':
				{
					if( nextTokenChar(aSchemaStream, '}') )
					{
						return( true );
					}
					break;
				}
				case '}':
				{
					return( true );
				}
				default:
				{
					return( false );
				}
			}
		}
	}

	return( false );
}


bool AvmTraceDirector::parseSchemaSpecBind(std::ifstream & aSchemaStream)
{
	if( nextTokenChar(aSchemaStream, '{') )
	{
		AVM_OPCODE bindOP = AVM_OPCODE_NULL;

		for( avm_offset_t anOffset = 0 ; (not mEndOfFile) ; ++anOffset )
		{
			if( nextTokenWord(aSchemaStream, "bind") )
			{
//				AVM_OS_COUT << TAB2 << "bind:> " << mParseLine << std::endl;

				bindOP = AVM_OPCODE_CHECK_SAT;
			}
			else
			{
				AVM_OS_WARN << "parseSchemaSpecBind:> "
						"Expected token << bind >> found << "
						<< mParseToken << " >> before << "
						<< mParseLine << " >> !!!" << std::endl;

				return( false );
			}

			if( nextTokenChar(aSchemaStream, '<') )
			{
				if( nextTokenWord(aSchemaStream, "eq") )
				{
					bindOP = AVM_OPCODE_EQ;
				}
				else if( nextTokenWord(aSchemaStream, "seq") )
				{
					bindOP = AVM_OPCODE_SEQ;
				}
				else if( nextTokenWord(aSchemaStream, "teq") )
				{
					bindOP = AVM_OPCODE_SEQ;
				}

				else if( nextTokenWord(aSchemaStream, "sat") )
				{
					bindOP = AVM_OPCODE_CHECK_SAT;
				}
				else if( nextTokenWord(aSchemaStream, "guard") )
				{
					bindOP = AVM_OPCODE_GUARD;
				}

				else if( nextTokenWord(aSchemaStream, "nop") ||
						nextTokenWord(aSchemaStream, "true") )
				{
					bindOP = AVM_OPCODE_NOP;
				}
				else if( nextTokenWord(aSchemaStream, "null") )
				{
					bindOP = AVM_OPCODE_NULL;
				}
				else
				{
					AVM_OS_WARN << "parseSchemaSpecBind:> "
							"Unexpected bind operator << "
							<< mParseLine << " >> !!!" << std::endl;

					return( false );
				}

				if( not nextTokenChar(aSchemaStream, '>') )
				{
					AVM_OS_WARN << "parseSchemaSpecBind:> "
							"Expected token << '>' >> found << "
							<< mParseLine << " >> !!!" << std::endl;
				}
			}

			mBindOP.push_back( bindOP );

			if( bindOP == AVM_OPCODE_NULL )
			{
				mSpecVariables.append( Symbol::REF_NULL );
			}
			else
			{
				if( nextTokenUFID(aSchemaStream) )
				{
//					AVM_OS_COUT << TAB2 << "var:> " << mParseToken << std::endl;

					ExecutableQuery XQuery( getConfiguration() );

					if( StringTools::startsWith(mParseToken,"spec::") )
					{
						mParseToken = mParseToken.substr(6);  // 6 == lenght("spec::")
					}

					Symbol bindVariable(
							XQuery.getVariableByQualifiedNameID(mParseToken) );

					if( bindVariable.valid() )
					{
//						AVM_OS_COUT << TAB2 << "symbol:> "
//								<< str_header( bindVariable ) << std::endl;

						mSpecVariables.append(bindVariable);
					}
					else
					{
						mSpecVariables.append( Symbol::REF_NULL );

						AVM_OS_WARN << "parseSchemaSpecBind:> "
								"Unfound bind spec variable << " << mParseToken
								<< " >> !!!" << std::endl;
					}
				}
				else
				{
					return( false );
				}
			}

			switch( nextTokenChar(aSchemaStream, ";}") )
			{
				case ';':
				{
					if( nextTokenChar(aSchemaStream, '}') )
					{
						return( true );
					}
					break;
				}
				case '}':
				{
					return( true );
				}
				default:
				{
					return( false );
				}
			}
		}
	}

	return( false );
}


/**
 * TRACE
 */
bool AvmTraceDirector::parseTrace(
		const std::string & aTraceLocation,
		const std::string & aTraceLabel)
{
	mEndOfFile = false;

	std::ifstream aTraceStream( aTraceLocation );

	bool isParseOK = aTraceStream.good();

	if( isParseOK )
	{
		isParseOK = false;

		if( parseTraceHeader(aTraceStream) )
		{
			mPendingTrace.clear();
			mPendingTrace.mTraceLabel = aTraceLabel;
			mPendingTrace.mTraceLocation = aTraceLocation;

			std::size_t count = 0;

			while( parseTraceUFID(aTraceStream) )
			{
				isParseOK = parseTraceNumeric(aTraceStream);

				if( isParseOK )
				{
					mPendingTrace.tid = ++TRACE_ID;

					mSelectedTrace = new AvmTraceDirective(mPendingTrace);
					mTableOfAnalyzingTrace.append( BF( mSelectedTrace ) );

					mTableOfAnalyzedTrace.append( mTableOfAnalyzingTrace.last() );

					mSelectedTrace->initFoldedBitset();

					mPendingTrace.clear();
					mPendingTrace.mTraceLabel = ( OSS()
							<< aTraceLabel << "#trace#" << (++count) );
					mPendingTrace.mTraceLocation = aTraceLocation;
				}
				else
				{
					break;
				}
			}
		}
	}

	aTraceStream.close();

	return( isParseOK );
}

bool AvmTraceDirector::parseTraceHeader(std::ifstream & aTraceStream)
{
//	AVM_OS_COUT << TAB2 << "HEADER :";
	for( avm_offset_t anOffset = 0 ; nextTokenID(aTraceStream) ; ++anOffset )
	{
//		AVM_OS_COUT << "> " << mParseToken << " <: " << std::flush;

		if( mParseToken != mTraceVariables[anOffset].getNameID() )
		{
			AVM_OS_WARN << "parseTraceHeader:> Expected token << "
					<< mTraceVariables[anOffset].getNameID()
					<< " >> found << " << mParseToken << " >> before << "
					<< mParseLine << " >> !!!" << std::endl;

			return( false );
		}

		if( mParseLine.empty() )
		{
//			AVM_OS_COUT << std::endl;

			if( nextTokenNewLine(aTraceStream) >= 0 )
			{
				return( true );
			}
		}
		else if( not nextTokenChar(aTraceStream, ';') )
		{
			AVM_OS_WARN << "parseTraceHeader:> Expected separator << ';' >> "
					"found << '" << mParseLine[0] << "' >> in << "
					<< mParseLine << " >> !!!" << std::endl;

			return( false );
		}
	}

	return( false );
}

bool AvmTraceDirector::parseTraceUFID(std::ifstream & aTraceStream)
{
	if( nextToken(aTraceStream) )
	{
//		AVM_OS_COUT << TAB2 << "QNID :> " << mParseToken << " <:" << std::endl;

		mPendingTrace.mTraceID = mParseToken;

		return( true );
	}

	return( false );
}

bool AvmTraceDirector::parseTraceNumeric(std::ifstream & aTraceStream)
{
	TP_ID = 0;

	avm_offset_t anOffset = 0;
//	AVM_OS_COUT << TAB2 << "LINE :";

	BFVector tpArray;

	while( nextToken(aTraceStream, "; " /*concat*/ SPACE_CHARS) )
	{
//		AVM_OS_COUT << "> " <<  mParseToken << " <: " << std::flush;

		if( not mTraceVariables[anOffset].getModifier().isVisibilityPrivate() )
		{
			if( mSpecVariables[anOffset].valid() )
			{
				tpArray.append( parseTraceNumeric(mSpecVariables[anOffset],
						mBindOP[anOffset], mParseToken) );
			}
			else
			{
				++mParseErrorCount;

				AVM_OS_WARN << "parseTraceNumeric:> "
						"No bind spec variable for trace << "
						<< str_header( mTraceVariables[anOffset] ) << " >> !!!"
						<< std::endl;

				tpArray.append( parseTraceNumeric(mTraceVariables[anOffset],
						mBindOP[anOffset], mParseToken) );
			}
		}
		++anOffset;

//		if( mParseErrorCount > 0 )
//		{
//			AVM_OS_COUT << std::endl;
//
//			return( false );
//		}

		if( mParseLine.empty() )
		{
			if( tpArray.singleton() )
			{
				mPendingTrace.append( tpArray.back() );

				tpArray.back().to< TracePoint >().tpid = ++TP_ID;

				tpArray.clear();
			}
			else if( tpArray.populated() )
			{
				mPendingTrace.save( mTracePoint = TracePoint::newComposite(
						AVM_OPCODE_AND, BF(new ArrayBF(tpArray)) ) );

				mTracePoint->tpid = ++TP_ID;

				tpArray.clear();
			}

//			AVM_OS_COUT << std::endl;

			if( (nextTokenNewLine(aTraceStream) > 0) || mEndOfFile )
			{
				break;
			}

//			AVM_OS_COUT << TAB2 << "LINE :" << std::flush;

			anOffset = 0;
		}
		else if( not nextTokenChar(aTraceStream, ';') )
		{
			return( false );
		}
	}

	return( (mParseErrorCount == 0) &&
			(anOffset == mTraceVariables.size()) );
}


BF AvmTraceDirector::parseTraceNumeric(const Symbol & aVar,
		AVM_OPCODE bindOP, const std::string & term)
{
	BF value;

	if( aVar.isTypedEnum() )
	{
		value = aVar.getTypeSpecifier().
				as< EnumTypeSpecifier >().getSymbolData().getByNameID(term);

		if( value.invalid() )
		{
			++mParseErrorCount;

			AVM_OS_WARN << "parseTraceNumeric:> Unexpected enum symbol << "
					<< term << " >> typed << "
					<< aVar.getTypeSpecifier().strT()
					<< " >> !!!" << std::endl;

			value = ExpressionConstructor::newString(term);
		}

		mTracePoint = new TracePoint( ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
				bindOP, nullptr, aVar.rawSymbol(), value);
	}
	else
	{
		value = ExpressionConstructor::newExpr(getConfiguration(), aVar, term);

		if( value.invalid() )
		{
			++mParseErrorCount;

			AVM_OS_WARN << "parseTraceNumeric:> Unexpected term << " << term
					<< " >> typed << " << aVar.getTypeSpecifier().strT()
					<< " >> !!!" << std::endl;

			value = ExpressionConstructor::newString(term);
		}

		mTracePoint = new TracePoint( ENUM_TRACE_POINT::TRACE_VARIABLE_NATURE,
				bindOP, nullptr, aVar.rawSymbol(), value);
	}

	mTracePoint->updateRID( getConfiguration().getMainExecutionData() );

	return( BF( mTracePoint ) );

//	return( value );

}

////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDirector::preprocess()
{
	AVM_OS_COUT << TAB << "preprocess< TRACE DIRECTOR >" << EOL_FLUSH;

	return( true );
}


bool AvmTraceDirector::postprocess()
{
	AVM_OS_COUT << TAB << "postprocess< TRACE DIRECTOR >" << EOL_FLUSH;

	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

/**
 * TRACE Analysis
 * parsing files & loading
 */
bool AvmTraceDirector::loadTrace()
{
	mTableOfAnalyzingTrace.clear();

	for( ; (mFileOffset < mFileCount) && (mParsedFileCount > 0) ;
			++mFileOffset , --mParsedFileCount )
	{
		if( parseTrace(mTableOfTraceFileLocation[mFileOffset],
				mTableOfTraceLabel[mFileOffset]) )
		{
			mTraceOffset = 0;
			mTraceCount  = mTableOfAnalyzingTrace.size();

			if( mTraceOffset < mTraceCount )
			{
//AVM_IF_DEBUG_LEVEL_FLAG2_AND( MEDIUM , PROCESSOR , TRACE ,( not mMinimizationFlag) )
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				mTableOfAnalyzingTrace.back().to<
						AvmTraceDirective >().traceMinimum(AVM_OS_LOG);

AVM_DEBUG_ELSE
				mTableOfAnalyzingTrace.back().to<
						AvmTraceDirective >().traceAbstract(AVM_OS_LOG);

AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				// update limit counter before return
				--mParsedFileCount;

				return( true );
			}
		}
		else
		{
			if( mTableOfAnalyzingTrace.nonempty() )
			{
				mTableOfAnalyzingTrace.back().to<
						AvmTraceDirective >().traceMinimum(AVM_OS_COUT);
			}

			AVM_OS_WARN << "AvmTraceDirector:> Processor plugin << "
					<< getParameterWObject()->getFullyQualifiedNameID() << " >> " << std::endl
					<< "Trace file analysis failed !!!" << std::endl
					<< "\tTrace file < " << mTableOfTraceLabel[mFileOffset]
					<< " :> " << mTableOfTraceFileLocation[mFileOffset]
					<< std::endl;
		}
	}

	return( false );
}


bool AvmTraceDirector::filteringInitialize()
{
	// At this step we deal with getExecutionQueue().getInitQueue()
	mInitialRootEC.append( getExecutionQueue().getInitQueue() );

	mFileOffset = 0;
	mFileCount  = mTableOfTraceFileLocation.size();

	if( loadTrace() )
	{
		mPendingTrace.clear();

		mSelectedTrace = mTableOfAnalyzingTrace[mTraceOffset].
				to_ptr< AvmTraceDirective >();
		mSelectedTrace->mStatus = AvmTraceDirective::PENDING;

		mPendingTrace.copyTrace( *mSelectedTrace );

		mCoverageOffset = 0;
		mSelectedTrace->mRequiredPointFlags[ mCoverageOffset ] = true;

		getSymbexRequestManager().postRequestContinue( this );

		return( true );
	}

	return( false );
}


bool AvmTraceDirector::prefilter()
{
//	ecQueue = &( getExecutionQueue().getReadyQueue() );
//	ecQueueIt = ecQueue->begin();
//	ecQueueItEnd = ecQueue->end();
//	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
//	{
//		if( prefilter(*ecQueueIt) )
//		{
//
//		}
//	}


	return( getExecutionQueue().hasReady() );
}


bool AvmTraceDirector::prefilter(ExecutionContext & anEC)
{
	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDirector::postfilter()
{
	initDriver();

	ecQueue = &( getExecutionQueue().getResultQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
	{
		if( mDirectiveEC.contains(*ecQueueIt) ||
			(*ecQueueIt)->isWeight(WEIGHT_SELECTED_ACHIEVABLE) )
		{
			checkDriver(*ecQueueIt);
		}
		else
		{
			ecChildIt = (*ecQueueIt)->begin();
			ecChildItEnd = (*ecQueueIt)->end();
			for( ; ecChildIt != ecChildItEnd ; ++ecChildIt )
			{
				(*ecChildIt)->setWeight( WEIGHT_WEAKLY_ACHIEVABLE );
			}
		}
	}

	if( electDriver() )
	{
		getSymbexRequestManager().postRequestGoalAchieved( this );
	}
	else if( mSelectedTrace->goalAborted() )
	{
		getSymbexRequestManager().postRequestGoalAchieved( this );
	}

	return( getExecutionQueue().hasResult() );
}

bool AvmTraceDirector::postfilter(ExecutionContext & anEC)
{
	return( true );
}


void AvmTraceDirector::initDriver()
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << std::endl << REPEAT("==========", 10) << std::endl;
	mPendingTrace.traceAbstract(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	coverageMax = 0;

	mCurrentEC.clear();
}


void AvmTraceDirector::checkDriver(ExecutionContext * anEC)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "DirectiveTrace:> " << anEC->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	ecChildItEnd = anEC->end();
	for( ecChildIt = anEC->begin() ; ecChildIt != ecChildItEnd ; ++ecChildIt )
	{
		(*ecChildIt)->setWeight( WEIGHT_WEAKLY_ACHIEVABLE );

		coverageCount = 0;

		for( const auto & itPoint : mPendingTrace.points )
		{
			const TracePoint & aTracePoint = itPoint.to< TracePoint >();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	if( coverageCount > coverageMax )
	{
		aTracePoint.toStream( AVM_OS_TRACE );
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			if( mTraceChecker.isSat(*(*ecChildIt), aTracePoint) )
			{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
	(*ecChildIt)->getwFlags().addCoverageElementTrace();

	(*ecChildIt)->addInfo(*this, itPoint);
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

				++coverageCount;

				if( not mFoldingFlag )
				{
					break;
				}
			}
			else
			{
				break;
			}
		}

		if( coverageCount >= coverageMax )
		{
			if( coverageCount > coverageMax )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	(*ecChildIt)->traceMinimum( AVM_OS_TRACE << "==>" );
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				coverageMax = coverageCount;

				mCurrentEC.clear();
			}

			mCurrentEC.append( *ecChildIt );
		}
	}
}


bool AvmTraceDirector::electDriver()
{
	if( coverageMax > 0 )
	{
		mDirectiveEC.clear();
		mDirectiveEC.splice( mCurrentEC );

		mSelectedTrace->setCoverage(mCoverageOffset , coverageMax);

		// GOAL UNACHIEVED
		if( coverageMax < mPendingTrace.size() )
		{
			mPendingTrace.points.pop_front( coverageMax );

			ecQueueIt = mDirectiveEC.begin();
			ecQueueItEnd = mDirectiveEC.end();
			for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
			{
				// Adding coverage information in Execution Context
				if( (not mMinimizationFlag) || (not (*ecQueueIt)->hasInfo()) )
				{
					(*ecQueueIt)->addInfo(*this, mTableOfAnalyzingTrace[mTraceOffset]);
				}

				(*ecQueueIt)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "HIT ! EC:> "; (*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}
		}

		else // GOAL ACHIEVED
		{
			mCoverageStatistics.addCoveredElement();

			mPendingTrace.mStatus = AvmTraceDirective::COVERED;

			ecQueueIt = mDirectiveEC.begin();
			ecQueueItEnd = mDirectiveEC.end();
			for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
			{
				(*ecQueueIt)->addInfo(*this, mTableOfAnalyzingTrace[mTraceOffset]);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_INFO << "GOAL ACHIEVED "
			<< mPendingTrace.strInfo() << " --> EC<" << AVM_STR_INDENT;
	(*ecQueueIt)->traceMinimum(AVM_OS_COUT);
	(*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
	(*ecQueueIt)->traceMinimum(AVM_OS_LOG);
	AVM_OS_INFO << " > " << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}

			mPendingTrace.points.clear();

			mSelectedTrace->mEC = *( mDirectiveEC.begin() );
			mSelectedTrace->setGoalAchieved( *this );
		}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << REPEAT("==========", 10) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return( mPendingTrace.points.empty() );
	}


	else
	{
		if( mConsecutiveFlag )
		{
			mSelectedTrace->mStatus = AvmTraceDirective::ABORTED;
			mSelectedTrace->mEC = *( mDirectiveEC.begin() );

AVM_IF_DEBUG_LEVEL_FLAG_AND( MEDIUM , PROCESSOR ,
		mPendingTrace.points.nonempty() )
	AVM_OS_INFO << "<ABORTED> " << mSelectedTrace->strInfo() << std::endl;
	mPendingTrace.points.front().to<
			TracePoint >().toStream(AVM_OS_COUT << "\t");
	mPendingTrace.points.front().to<
			TracePoint >().toStream(AVM_OS_TRACE << "\t");
	mPendingTrace.points.front().to<
			TracePoint >().toStream(AVM_OS_LOG << "\t");
	AVM_OS_INFO << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG_AND( MEDIUM , PROCESSOR )
		}

		mCurrentEC.clear();
		mCurrentEC.splice( mDirectiveEC );

		ecQueueIt = mCurrentEC.begin();
		ecQueueItEnd = mCurrentEC.end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			ecChildIt = (*ecQueueIt)->begin();
			ecChildItEnd = (*ecQueueIt)->end();
			for( ; ecChildIt != ecChildItEnd ; ++ecChildIt )
			{
				(*ecChildIt)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

				mDirectiveEC.append( *ecChildIt );
			}
		}

		return( false );
	}
}


void AvmTraceDirector::selectDriver()
{
	mCoverageOffset = 0;
	saveCoverageMax = 0;

	BFList::const_raw_iterator< GenericInfoData > itInfo;
	BFList::const_raw_iterator< GenericInfoData > endInfo;

	while( true )
	{
		initDriver();

		ecQueueIt = mDirectiveEC.begin();
		ecQueueItEnd = mDirectiveEC.end();
		for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
		{
			checkDriver( *ecQueueIt );
		}

		if( electDriver() )
		{
			ecQueueIt = mDirectiveEC.begin();
			ecQueueItEnd = mDirectiveEC.end();
			for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
			{
				if( (*ecQueueIt)->hasInfo(*this) )
				{
					if( mSelectedTrace->mRedundantTrace == nullptr )
					{
						itInfo = (*ecQueueIt)->getInfos().begin();
						endInfo = (*ecQueueIt)->getInfos().end();
						for( ; itInfo != endInfo ; ++itInfo )
						{
							if( itInfo->isInfo(*this) &&
								itInfo->getData().is< AvmTraceDirective >() )
							{
								mProcessedTrace = itInfo->getData().
										to_ptr< AvmTraceDirective >();

								if( mProcessedTrace != mSelectedTrace )
								{
									mSelectedTrace->mRedundantTrace = mProcessedTrace;

									mSelectedTrace->mRedundantEC.append( *ecQueueIt );

									break;
								}
							}
						}
					}
				}
			}

			if( mSelectedTrace->mRedundantTrace != nullptr )
			{
				++mRedundancyCount;

				mSelectedTrace->mStatus = AvmTraceDirective::REDUNDANT;
				mTableOfRedundantTrace.append( mTableOfAnalyzingTrace[mTraceOffset] );

				AVM_OS_VERBOSITY_MINIMUM( AVM_OS_INFO )
						<< std::endl << "Found REDUNDANCE :"
						<< mRedundancyCount << "> "
						<< mPendingTrace.strInfo() << std::endl;
			}

			break;
		}

		else if( mSelectedTrace->goalAborted() )
		{
			break;
		}
		else
		{
			if( saveCoverageMax < coverageMax )
			{
				mNextRootEC.clear();

				saveCoverageMax = coverageMax;
			}

			ecQueueIt = mDirectiveEC.begin();
			ecQueueItEnd = mDirectiveEC.end();
			for( ; ecQueueIt != ecQueueItEnd ; )
			{
				if( (*ecQueueIt)->isEvaluated() )
				{
					++ecQueueIt;
				}
				else
				{
					mNextRootEC.append( *ecQueueIt );

					if( (*ecQueueIt)->hasInfo() )
					{
						itInfo = (*ecQueueIt)->getInfos().begin();
						endInfo = (*ecQueueIt)->getInfos().end();
						for( ; itInfo != endInfo ; ++itInfo )
						{
							if( itInfo->isInfo(*this) &&
								itInfo->getData().is< AvmTraceDirective >() )
							{
								mProcessedTrace = itInfo->getData().
										to_ptr< AvmTraceDirective >();

								if( mProcessedTrace != mSelectedTrace )
								{
									mProcessedTrace->mRedundantEC.append(*ecQueueIt);

									if( mProcessedTrace->mRedundantTrace == nullptr )
									{
										mProcessedTrace->mRedundantTrace = mSelectedTrace;

										++mRedundancyCount;
										mTableOfRedundantTrace.append(
												itInfo->getData() );

										mProcessedTrace->mStatus =
												AvmTraceDirective::REDUNDANT;

										AVM_OS_VERBOSITY_MINIMUM( AVM_OS_INFO )
												<< std::endl
												<< "Found REDUNDANCE :> "
												<< mProcessedTrace->strInfo()
												<< std::endl;
									}
								}
							}
						}
					}

					ecQueueIt = mDirectiveEC.erase( ecQueueIt );
				}
			}

			if( mDirectiveEC.empty() )
			{
				break;
			}
		}
	}
}


void AvmTraceDirector::initWaitingQueue()
{
	ecQueueIt = mNextRootEC.begin();
	ecQueueItEnd = mNextRootEC.end();
	for( ; ecQueueIt != ecQueueItEnd ; ++ecQueueIt )
	{
		(*ecQueueIt)->setWeight( WEIGHT_SELECTED_ACHIEVABLE );

		getExecutionQueue().pushWaiting( *ecQueueIt );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << "ROOT ! EC:> "; (*ecQueueIt)->traceMinimum(AVM_OS_TRACE);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}
}


/**
 * PROCESSOR REQUEST API :> CONITNUE
 */
void AvmTraceDirector::handleRequestContinue()
{
	++mTraceOffset;

	do
	{
		for( ; mTraceOffset < mTraceCount ; ++mTraceOffset )
		{
			mNextRootEC.clear();
			mDirectiveEC.clear();
			mCurrentEC.clear();

			mPendingTrace.clear();

			mSelectedTrace = mTableOfAnalyzingTrace[mTraceOffset].
					to_ptr< AvmTraceDirective >();
			mSelectedTrace->mStatus = AvmTraceDirective::PENDING;

			mPendingTrace.copyTrace( *mSelectedTrace );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_TRACE << std::endl << std::endl
			<< mPendingTrace.strInfo() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			mDirectiveEC.append( mInitialRootEC );

			selectDriver();

			if( mSelectedTrace->goalAborted() )
			{
				AVM_OS_INFO << "FAILED< "  << mSelectedTrace->strStatus() << " :> "
						<< mSelectedTrace->strInfo() << std::endl << std::endl;
			}
			else if( mSelectedTrace->goalPending() )
			{
				initWaitingQueue();

				if( getExecutionQueue().hasWaiting() )
				{
					getSymbexRequestManager().postRequestContinue( this );

					return;
				}
			}
			else if( not mSelectedTrace->goalAchieved() )
			{
				AVM_OS_INFO << REPEAT("==========", 10) << std::endl
						<< "BUG< "  << mSelectedTrace->strStatus() << " :> "
						<< mSelectedTrace->strInfo() << std::endl
						<< REPEAT("==========", 10) << std::endl;
			}
		}

		// Loadind next file of Traces !
		++mFileOffset;
	}
	while( loadTrace() );
}


/**
 * PROCESSOR REQUEST API :> GOAL_ACHIEVED
 */
void AvmTraceDirector::handleRequestGoalAchieved()
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	if( mSelectedTrace->goalAchieved() )
	{
		AVM_OS_INFO << "GOAL ACHIEVED :> " << mSelectedTrace->strInfo()
				<< std::endl << std::endl;
	}
	else
	{
		AVM_OS_INFO << "FAILED< "  << mSelectedTrace->strStatus() << " :> "
				<< mSelectedTrace->strInfo() << std::endl << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	if( mFileOffset < mFileCount )
	{
		getExecutionQueue().handleRequestStop();
	}
	else
	{
		getSymbexRequestManager().postRequestStop( this );
	}
}


/**
 * FILTERING FINALIZE
 */
bool AvmTraceDirector::filteringFinalize()
{
	if( not BaseCoverageFilter::filteringFinalize() )
	{
		return( false );
	}

	mListOfLeafEC.clear();

	// ELAGAGE DANS TOUT LE GRAPH!!!!!
	computeLeafEC(getConfiguration().getExecutionTrace(), mListOfLeafEC);

	/**
	 * Normalizing
	 */
	if( mNormalizationFlag )
	{
		finalizeTrace();
	}

	/**
	 * Reporting
	 */
	SerializerFeature::beginStream();
	while( SerializerFeature::hasStream() )
	{
		reportTrace( SerializerFeature::currentStream() );
	}
	SerializerFeature::closeStream();

	return( true );
}


void AvmTraceDirector::finalizeTrace() const
{
	std::string redondancyFolder =
			SerializerFeature::getFolder().location + VFS::PathSeparator + "redundance";

	std::string traceFile;

	if( not VFS::checkWritingFolder(redondancyFolder) )
	{
		return;
	}

	BFVector::const_raw_iterator< AvmTraceDirective >
	itTrace = mTableOfRedundantTrace.begin();
	BFVector::const_raw_iterator< AvmTraceDirective >
	endTrace = mTableOfRedundantTrace.end();
	for( ; itTrace < endTrace ; ++itTrace )
	{
		switch( (itTrace)->mStatus )
		{
			case AvmTraceDirective::REDUNDANT:
			{
				traceFile = VFS::relativeProjectPath((itTrace)->mTraceLocation,
						SerializerFeature::getFolder().location + VFS::PathSeparator);

				if( (itTrace)->mReducedFlag )
				{
					traceFile = VFS::prefixFilename(traceFile, "diversity_" );
				}

				if( not VFS::moveToFolder(traceFile, redondancyFolder) )
				{
					AVM_OS_WARN << "finalizeTrace:> Failed to move trace file << "
							<< traceFile << " >> to << " << redondancyFolder
							<< " >> !!!" << std::endl;
				}

				break;
			}

			default:
			{
				break;
			}
		}
	}
}

////////////////////////////////////////////////////////////////////////////////
// DEBUG PROCESSING API
////////////////////////////////////////////////////////////////////////////////

bool AvmTraceDirector::debugEvalCommandImpl()
{
	if( dbgDecodeCommand("-->") )
	{
		dbgCommandDirectiveTrace();

		return( true );
	}

	return( false );
}


void AvmTraceDirector::dbgCommandDirectiveTrace()
{
}


} /* namespace sep */
