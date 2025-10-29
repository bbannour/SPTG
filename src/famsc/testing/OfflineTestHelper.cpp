/*******************************************************************************
 * Copyright (c) 2019 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 01 oct. 2019
 *
 * Contributors:
 *  Jose Escobedo (CEA LIST) jose.escobedo@cea.fr
 *  Mathilde Arnaud (CEA LIST) mathilde.arnaud@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "OfflineTestHelper.h"

#include <common/BF.h>

#include <famsc/testing/OfflineTestProcessor.h>
#include <fml/expression/AvmCode.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>

#include <fml/trace/TraceFactory.h>
#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>


namespace sep
{

/*
 * Parse FAM Configuration
 * Utils
 */
//TODO : parameterize input format
bool OfflineTestHelper::parseMergedTrace(
		TraceFactory & aTraceFactory, const std::string & format,
		const std::string & filePath,
		TraceSequence & aMergeTrace, const BF & theTimeVar)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "File path of merged trace: " << filePath << std::endl
	<< "Trace format: " << format << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	std::ifstream fileTrace;
	fileTrace.open(filePath, std::ifstream::in);
	if( fileTrace.is_open() )
	{
		if( format.starts_with("BASIC") )
		{
			return( aTraceFactory.parseBasicXliaTrace(
					aMergeTrace, fileTrace, theTimeVar) );
		}
		else //if( format.starts_with("BASIC") )
		{
			return( aTraceFactory.parseBasicTrace(
					aMergeTrace, fileTrace, theTimeVar) );
		}
	}
	else
	{
		AVM_OS_WARN << "Error: cannot open file "
				<< filePath << std::endl;
	}

	return( false );
}


bool OfflineTestHelper::parseMergedTrace(
		TraceFactory & aTraceFactory, const std::string & filePath,
		TraceSequence & aMergeTrace, const BF & theTimeVar)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "File path of merged trace: " << filePath << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	std::ifstream fileTrace;
	fileTrace.open(filePath, std::ifstream::in);
	if( fileTrace.is_open() )
	{
		return( aTraceFactory.parseBasicTrace(
				aMergeTrace, fileTrace, theTimeVar) );
	}
	else
	{
		AVM_OS_WARN << "Error: cannot open file "
				<< filePath << std::endl;
	}

	return( false );
}


bool OfflineTestHelper::parseTestPurpose(
		const std::string & filePath, TraceSequence & testPurpose)
{
	/*
	 * This function parses the test purpose given in a file
	 * as a sequence of transitions.
	 * If filePath is empty, no test purpose is specified
	 * The sequence of transitions is stored in the trace element testPurpose
	 */
	if( filePath == "" )
	{
		AVM_OS_LOG << "Warning: No test purpose specified! " << std::endl;
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "The file path of the test purpose to parse is: "
			<< filePath << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		std::ifstream testPurposeFile;
		testPurposeFile.open(filePath, std::ifstream::in);
		if( testPurposeFile.is_open() )
		{
			std::string oneLine;

			while (testPurposeFile.good())
			{
				std::getline(testPurposeFile, oneLine);

				TraceFactory::appendTransitionPoint(
						mProcessorUnit.getConfiguration(), testPurpose, oneLine);
			}
		}
		else
		{

		AVM_OS_WARN << "Error: Error while reading test purpose file "
				<< filePath << std::endl;
		return false;
		}
	}
	return true;
}


/*
 * Input/Output Trace
 * Utils
 */
bool OfflineTestHelper::hasIOTrace(const BF & anElement)
{
	if( anElement.invalid() )
	{
		return (false);
	}
	else if( anElement.is< AvmCode >() )
	{
		const AvmCode & theAC = anElement.to< AvmCode >();
		switch (theAC.getAvmOpCode())
		{
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_OUTPUT:
			{
				return true;
			}

			case AVM_OPCODE_ASSIGN_NEWFRESH :
			{
				return false;
			}

			default:
			{
				for( const auto & itOperand : theAC.getOperands() )
				{
					if( hasIOTrace( itOperand ) )
					{
						return true;
					}
				}

				return false;
			}
		}
	}
	else if( anElement.is< ExecutionConfiguration >() )
	{
		return (hasIOTrace(anElement.to< ExecutionConfiguration >().getCode()));
	}

	return false;
}


/*
 * Test Purpose
 * Utils
 */
bool OfflineTestHelper::testPurposeContainsElement(
		TraceSequence & aTestPurpose, const BF & anElement)
{
	if( anElement.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & theExecConf =
				anElement.to< ExecutionConfiguration >();

		if( theExecConf.hasCode() )
		{
			if( theExecConf.isTransition() )
			{
				if( aTestPurpose.containsObject(theExecConf.getTransition()) )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Transition found in TP !"
			<< theExecConf.toTransition().getAstNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					return true;
				}

				//adding case where no test purpose is specified
				//should not be used any more, treated in postprocess
				/*
				else if( aTestPurpose.points.empty() )
				{
					return true;
					AVM_OS_WARN << "NB: The verdict was computed with no test purpose. " << std::endl;
				}*/
			}
		}
	}

	else if( anElement.is< AvmCode >() )
	{
		const AvmCode & theAC = anElement.to< AvmCode >();

		for( const auto & itOperand : theAC.getOperands() )
		{
			if( testPurposeContainsElement(aTestPurpose, itOperand) )
			{
				return true;
			}
		}
	}

	return false;
}



/*
 * Local Observable
 * Utils
 */
void OfflineTestHelper::makeLocalObs(
		TraceSequence & anObs, TraceSequence & aTrace, bool timedFlag)
{
	/*
	 * Creates a single observation from the trace aTrace.
	 * A single observation can consist of multiple structures of type
	 * OneObs, since we may have multiple communication channels
	 */

//		anObs.clear();
	anObs.points.clear();

	// If the system is timed, a single observation consists of
	// the time delay
	// all communication actions occurring before the next time delay
	if (aTrace.points.nonempty() && timedFlag)
	{
		// start with time obs
		anObs.points.append( aTrace.points.first() );

		BFList::raw_iterator< TracePoint > itPoint = aTrace.points.begin();
		BFList::raw_iterator< TracePoint > endPoint = aTrace.points.end();
		for( ++itPoint ; (itPoint != endPoint) ; ++itPoint )
		{
			if( itPoint->isTime() )
			{
				break;
			}
			else
			{
				anObs.points.append(*itPoint);
			}
		}
	}

	else if (aTrace.points.nonempty())
	{
		anObs.copyTrace(aTrace);
	}

//		if (aTrace.points.size() >0)
//		{
//
//		}

}

//void removeOneObs(TraceSequence & aTrace)
//{
//	/*
//	 * Deletes one observation from the trace.
//	 * We assume that one observation consists of a delay and
//	 * of one or more inputs/outputs (up to the next delay).
//	 */
//
//	if (aTrace.points.size() >0)
//	{
//		// start with time obs
//		aTrace.points.remove_first();
//
//		if (aTrace.points.size() >0)
//		{
//			BFList::const_iterator itPoint = aTrace.points.begin();
//			BFList::const_iterator endPoint = aTrace.points.end();
//			TracePoint * aTracePoint = (*itPoint).to_ptr< TracePoint >();
//			while ( (itPoint != endPoint) && !aTracePoint->isTime())
//			{
//				aTrace.points.remove_first();
//				aTracePoint = (*itPoint).to_ptr< TracePoint >();
//			}
//
//		}
//	}
//}



////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////


void OfflineTestHelper::printTrace(const TraceSequence & aTrace,
		const std::string & title, const std::string & tab)
{
	AVM_OS_LOG << tab << title << std::endl << AVM_TAB_INDENT;

	aTrace.toStream( AVM_OS_LOG );

	AVM_OS_LOG << END_INDENT << std::endl;

//		TraceSequence::const_iterator it = aTrace.begin();
//		for( ; it != aTrace.end() ; ++it )
//		{
////		if ( (*it).first().is< InstanceOfData >()
//				&& (theTimedVarsVector.getAstNameID()
//					== (*it).first().to< InstanceOfData >().getAstNameID()) )
////		{
////			AVM_OS_LOG << TAB << "XXXXXXXXXXXXXXtimevar: "
////						<< (*it).first().str() << std::endl;
////		}
//			//AVM_OS_LOG << TAB << "XXXXXXXXXXXXXX22222: "
//					<< (*it).first().to< InstanceOfData >().getAstNameID()
//					<< std::endl;
//			if ( (*it).first().is< InstanceOfData >()
//				&& (theTimeVarInstance->getAstNameID()
//					== (*it).first().to< InstanceOfData >().getAstNameID()) )
//			{
//				// it is a time var, print first and second values
//				AVM_OS_LOG << tab << "timevar: " << (*it).first().str() << std::endl
//						<< tab << "value: " << (*it).second().str() <<  std::endl
//						<< tab << REPEAT("==========", 5) << std::endl;
//			}
//			else
//			{
//				// it is a port, sens, value observation
//			AVM_OS_LOG << tab << "port: " << (*it).first().str() << std::endl
//					<< tab << "sens: " << (*it).second().str() <<  std::endl
//					<< tab << "value: " << (*it).at(3).str() << std::endl
//					<< tab << REPEAT("==========", 5) << std::endl;
//			}
//		}
}



} /* namespace sep */
