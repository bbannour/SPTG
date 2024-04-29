/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: fev. 2012
 *
 * Contributors:
 *  Jose Escobedo (CEA LIST) jose.escobedo@cea.fr
 *  Mathilde Arnaud (CEA LIST) mathilde.arnaud@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "OfflineTestProcessor.h"

#include <algorithm>
#include <fstream>
#include <string>
#include <sstream>
#include <iterator>

//#include <boost/algorithm/string.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/format.hpp>

#include <util/avm_util.h>
#include <util/avm_vfs.h>

#include <builder/Builder.h>

#include <computer/primitive/AvmCommunicationFactory.h>
#include <computer/PathConditionProcessor.h>

#include <collection/Typedef.h>

#include <fml/numeric/Float.h>
#include <fml/numeric/Number.h>

#include <fml/expression/ExpressionConstant.h>
#include <fml/expression/ExpressionConstructor.h>
#include <fml/expression/ExpressionTypeChecker.h>

#include <fml/executable/ExecutableQuery.h>
#include <fml/executable/InstanceOfData.h>

#include <fml/infrastructure/ComProtocol.h>

#include <fml/operator/OperatorLib.h>

#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionInformation.h>
#include <fml/runtime/RuntimeQuery.h>

#include <fml/template/TimedMachine.h>

#include <fml/trace/TraceFactory.h>

#include <famcore/queue/ExecutionQueue.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
OfflineTestProcessor::OfflineTestProcessor(
		SymbexControllerUnitManager & aControllerUnitManager,
		const WObject * wfParameterObject)
: RegisteredProcessorUnit(aControllerUnitManager , wfParameterObject,
		AVM_PREPOST_FILTERING_STAGE | AVM_POST_PROCESSING_STAGE,
		PRECEDENCE_OF_TEST_OFFLINE),
OfflineTestHelper( *this ),

INFO_OFFLINETEST_DATA( new Identifier( "OFFLINE_TEST" ) ),
INFO_OFFLINETEST_DATA_PASS( new Identifier( "OFFLINE_TEST_PASS" ) ),
INFO_OFFLINETEST_DATA_INCONC( new Identifier( "OFFLINE_TEST_INCONC" ) ),
INFO_OFFLINETEST_DATA_FAIL( new Identifier( "OFFLINE_TEST_FAIL" ) ),
INFO_OFFLINETEST_TP_PATH( new Identifier( "TEST_PURPOSE_PATH" ) ),
INFO_OFFLINETEST_TARGET_STATE( new Identifier( "TARGET_STATE" ) ),

theVerdictKind( VERDICT_UNDEFINED_KIND ),

theSolverKind( SolverDef::SOLVER_CVC4_KIND ),
mFoldingFlag( true ),
mStepScheduler( AVM_OPCODE_SEQUENCE ),

theTrace( ),
//theMergeTrace( ),

theTimedVarsVector( ),
traceInPath( 0 ),
verdictEmitted( false ),
theVerdict( ),
theTestPurpose( ),
theTimeVarInstance( nullptr ),
theLeavesECVector( ),

theSmallestTraceEC( nullptr ),
theTraceCoverageBitSet( ),
theUncoverageTraceReportingCount( 42 ),

timeReferenceInstance( nullptr ),
theObsSignals( ),
theTraceFilter( (wfParameterObject != WObject::_NULL_) ?
		wfParameterObject->getNameID() : "OfflineTestProcessor" ),
theErasedNodes( 0 ),
timedFlag( ),

theMainExecutionData( getConfiguration().getMainExecutionData() )
{
	//!! NOTHING
}

/*
prototype process::offline_test "offline_test" as &avm::processor.OFFLINETEST is
	section PROPERTY
		// 'OMEGA' | 'CVC4' | 'Z3' | 'YICES'
		@solver = 'CVC4';
	endsection PROPERTY

	section MERGED_TRACE
		@mergedTraceFile="merged_trace.txt";
		//optional
		@timeVar="spec::system.deltaT";
		//optional
		@testPurposeFile="test_purpose.txt";
	endsection MERGED_TRACE

	section TIME_HANDLING
		//optional
		@currentTime = "inst::system.T";
	endsection TIME_HANDLING

	// deprecated
	section OBSERVABLE_SIGNAL
		@machine = "m1";
		@port= "p1";
		@sens = "?";
		@machine = "m2";
		@port= "p2";
		@sens = "!";
	endsection OBSERVABLE_SIGNAL

	section OBSERVABLE
		@input = "machine_instance1->signal1";
		@output = "machine_instance2->signal2";
		@input = "machine_instance3->signal1";
		@output = "machine_instance3->signal2";
	endsection

	section CONTROLLABLE
		@input = "machine_instance3->signal1";
	endsection CONTROLLABLE


endprototype
 */

////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool OfflineTestProcessor::configureImpl()
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("property", "PROPERTY"));
	std::string format;
	if( thePROPERTY != WObject::_NULL_ )
	{
		std::string theSolverID =
				Query::getWPropertyString(thePROPERTY, "solver", "");

		theSolverKind = SolverDef::toSolver(
				theSolverID, SolverDef::DEFAULT_SOLVER_KIND);

		//TODO: add possibility to parameterize input format
		//for the moment, two formats given as-is:
		// the historical format and the basic xlia trace format
		format = Query::getWPropertyString(
				thePROPERTY, "format", "BASIC#XLIA");
	}
	else
	{
		theSolverKind = SolverDef::DEFAULT_SOLVER_KIND;
		format = "BASIC#XLIA";
	}

	// The Folding Flag when checking Trace Point satisfiability in one EC
	mFoldingFlag  = Query::getRegexWPropertyBoolean(
			thePROPERTY, PREFIX_WID("trace", "folding"), true);

	// Trace step scheduling, in anEC->ioTrace, if folding is true
	std::string strScheduler = Query::getRegexWPropertyString(
			thePROPERTY, PREFIX_WID("step", "scheduler"), "|;|");
	mStepScheduler = OperatorLib::toOpcode(strScheduler, AVM_OPCODE_NULL);
	switch( mStepScheduler )
	{
		case AVM_OPCODE_NULL:
		{
			if( strScheduler == "ordered" )
			{
				mStepScheduler = AVM_OPCODE_SEQUENCE;
			}
			else if( strScheduler == "unordered" )
			{
				mStepScheduler = AVM_OPCODE_INTERLEAVING;
			}
			break;
		}
		case AVM_OPCODE_SEQUENCE:
		case AVM_OPCODE_INTERLEAVING:
		{
			break;
		}

		case AVM_OPCODE_ATOMIC_SEQUENCE:
		case AVM_OPCODE_SEQUENCE_SIDE:
		case AVM_OPCODE_SEQUENCE_WEAK:
		default:
		{
			mStepScheduler = AVM_OPCODE_SEQUENCE;
			break;
		}
	}

	const WObject * theMergedTrace = Query::getRegexWSequence(
			mParameterWObject, OR_WID2("merged_trace", "MERGED_TRACE"));
//	const WObject * theTimeHandling = Query::getRegexWSequence(
//			mParameterWObject , OR_WID2("time_handling", "TIME_HANDLING") );

	TraceFactory traceFactory(getConfiguration(), ENV,
			mParameterWObject, ExecutableForm::nullref());

	// Retrieving time info from the xfsp

	BF aTimeVarInstance;

	if( TimedMachine::SYSTEM_VAR_DELTA_TIME != nullptr )
	{
		ExecutableQuery XQuery( getConfiguration() );

		timeReferenceInstance = XQuery.getVariableByAstElement(
			(* TimedMachine::SYSTEM_VAR_GLOBAL_TIME) ).to_ptr< InstanceOfData >();


		aTimeVarInstance = XQuery.getVariableByAstElement(
				(* TimedMachine::SYSTEM_VAR_DELTA_TIME) );

		theTimeVarInstance = aTimeVarInstance.to_ptr< InstanceOfData >();

		timedFlag = true;
	}
	// TODO: changing time management, getting information directly from the xfsp
	else
	{
		AVM_OS_LOG << "No time parameter found!" << std::endl;
		timedFlag = false;
	}

	/*
	else
	{
		std::string theCurrentTimeVar =
				Query::getWPropertyString(theTimeHandling, "currentTime", "");

		if( not theCurrentTimeVar.empty() )
		{
			timeReferenceInstance = RQuery.searchVariable(
					theMainExecutionData, theCurrentTimeVar);
			if( timeReferenceInstance.invalid() )
			{
				AVM_OS_WARN << "Unfound currentTime< " << theCurrentTimeVar
						<< "> parameter!" << std::endl;

				mConfigFlag = false;
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound currentTime parameter!" << std::endl;

			mConfigFlag = false;
		}


		std::string timeVar =
				Query::getWPropertyString(theMergedTrace, "timeVar", "");

		if( not timeVar.empty() )
		{
			theTimeVarInstance = RQuery.searchVariable(
					theMainExecutionData, timeVar);
			if( theTimeVarInstance.invalid() )
			{
				AVM_OS_LOG << "Unfound timeVar < " << timeVar << "> parameter!"
						<< std::endl;

				mConfigFlag = false;
			}
		}
		else
		{
			AVM_OS_WARN << "Unfound timeVar parameter!" << std::endl;

			mConfigFlag = false;
		}
	}*/

	std::string theMergedTracePath =
			Query::getWPropertyString(theMergedTrace, "mergedTraceFile", "");

	theMergedTracePath = VFS::native_path(
			theMergedTracePath, VFS::ProjectSourcePath);

	// initializing theTrace
	if( not parseMergedTrace(traceFactory, format,
			theMergedTracePath, theTrace, aTimeVarInstance) )
	{
		AVM_OS_WARN << "Error: Error while parsing the trace! " << std::endl;

		mConfigFlag = false;

		//TODO: check that this is useless and erase it
		// initializing theMergeTrace
		/*if( not parseMergedTrace(traceFactory,
				theMergedTracePath, theMergeTrace, theTimeVarInstance) )
		{
			AVM_OS_WARN << "Error: Error while parsing merged trace! " << std::endl;

			mConfigFlag = false;
		}*/
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "The merge trace (sequence of duration/input/output) is: " << std::endl;
	theTrace.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	theTrace.setTracePointID(0);

	theTraceCoverageBitSet.resize( theTrace.size() , false );

	std::string testPurposePath =
			Query::getWPropertyString(theMergedTrace, "testPurposeFile", "");

	if( not testPurposePath.empty() )
	{
		testPurposePath = VFS::native_path(
				testPurposePath, VFS::ProjectSourcePath);

		if( not parseTestPurpose(testPurposePath, theTestPurpose) )
		{
			AVM_OS_WARN << "Error: Error while parsing test purpose! " << std::endl;

			mConfigFlag = false;
		}
	}


AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "The parsed trace is: " << std::endl;
	printTrace(theTrace);

	AVM_OS_LOG << "The test purpose (sequence of transition names) is: " << std::endl;
	theTestPurpose.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )


	// Configuration of OBSERVABLE SIGNAL
	const WObject * theObservableSignals = Query::getRegexWSequence(mParameterWObject,
			OR_WID2("observable", "OBSERVABLE"), WObject::_NULL_);

	//TODO: tests !
	// if nothing is declared in the configuration file
	// the observable are set to be the signals appearing in the trace
	if( (theObservableSignals == WObject::_NULL_) ||
		theObservableSignals->hasnoOwnedElement() )
	{
		AVM_OS_LOG << "Warning : Observable ports are not configured" << std::endl
				<< "Deducing observable ports from the trace" <<std::endl;

		BFList::raw_iterator< TracePoint > itPoint = theTrace.points.begin();
		BFList::raw_iterator< TracePoint > endPoint = theTrace.points.end();
		for( ; (itPoint != endPoint) ; ++itPoint )
		{
			if( (not itPoint->isTime())
				&& (not theObsSignals.containsPoint(itPoint, false)))
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "Adding point: " << (* itPoint) <<  std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
					theObsSignals.points.append(*itPoint);
			}
		}
	}
	// if the observable section contains something
	// the observable signals are configured accordingly
	else
	{
		mConfigFlag = traceFactory.configure(theObservableSignals, theObsSignals)
				&& mConfigFlag;
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_LOG << "Configuration of OBSERVABLE SIGNAL: " << std::endl;
	theObsSignals.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )


	// Configuration of CONTROLLABLE SIGNAL
	mConfigFlag = theTraceFilter.configure(
			ENV, getParameterWObject(), "controllable", "CONTROLLABLE")
			&& mConfigFlag;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )
	AVM_OS_LOG << "Configuration of CONTROLLABLE SIGNAL: " << std::endl;
	theTraceFilter.toStream( AVM_OS_LOG << AVM_TAB_INDENT );
	AVM_OS_LOG << END_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , CONFIGURING )

	theUncoverageTraceReportingCount = Query::getRegexWPropertySizeT(
			thePROPERTY, PREFIX_WID("trace", CONS_WID2("reporting", "size")),
			theUncoverageTraceReportingCount, AVM_NUMERIC_MAX_SIZE_T);


	// initialization
	traceInPath = 0;
	verdictEmitted = false;
	theVerdict = "";
	theErasedNodes = 0;

	return mConfigFlag;
}


/**
 * SPIDER TRACE
 */
void OfflineTestProcessor::traceInitSpider(OutStream & os) const
{
	boost::format formatter(mSpiderInitTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}

void OfflineTestProcessor::traceStepSpider(
		OutStream & os, const ExecutionContext & anEC) const
{
	boost::format formatter(mSpiderStepTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}

void OfflineTestProcessor::traceStopSpider(OutStream & os) const
{
	boost::format formatter(mSpiderStopTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}

/**
 * EVAL TRACE
 */
void OfflineTestProcessor::traceMinimumPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	boost::format formatter(mPreEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}


void OfflineTestProcessor::traceDefaultPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	os << "coverage< " << getParameterWObject()->getNameID() << " >: "
			<< theTraceCoverageBitSet.count() << " / "
			<< theTrace.size() << std::endl;
}


void OfflineTestProcessor::traceBoundEval(OutStream & os) const
{
	boost::format formatter(mBoundEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}


void OfflineTestProcessor::reportEval(OutStream & os) const
{
	boost::format formatter(mReportEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << formatter
			% theTraceCoverageBitSet.count()
			% theTrace.size()
			<< std::flush;
}


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void OfflineTestProcessor::reportDefault(OutStream & out) const
{
	reportHeader(out, "AVM OFF-LINE TEST ");

	out << EMPHASIS(theVerdict, '=', 80);

	if( thePassEC.nonempty() )
	{
		out << "PASS State:" << std::endl;
		for( const auto & itEC : thePassEC )
		{
			out << "\t" << itEC->str() << std::endl;
		}
	}

	if( (theVerdictKind == VERDICT_FAIL_KIND)
		&& (theSmallestTraceEC != nullptr) )
	{
		out << "The smallest trace that has failed started with :" << std::endl;

//		theSmallestTraceEC->getInformation()
//				->getUniqOfflineTestProcessorInfo()
//				->getLocalTrace().toStream(out, theUncoverageTraceReportingCount);
//
//		out << "The Coverge bitset : " << theTraceCoverageBitSet << std::endl;

		theTrace.toStream(out, theTraceCoverageBitSet,
				theUncoverageTraceReportingCount);
	}
}


////////////////////////////////////////////////////////////////////////////////
// PRE-PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool OfflineTestProcessor::preprocess()
{
	AVM_OS_WARN << "OfflineTestProcessor::preprocess()" << std::endl;

	return( true );
}

////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool OfflineTestProcessor::AssignValuesIfObservable(
		ExecutionContext & anExecutionContext, TraceSequence & localTrace)
{
	bool valueAssigned = false;
	if( anExecutionContext.hasIOElementTrace() )
	{
		const BF & theBF = anExecutionContext.getIOElementTrace();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "OFFLINE TEST:: About to parse the trace: " << std::endl
			<< theBF.toString() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

		//DONE : change hasIO for matchesIO in a smart way

		valueAssigned = matchesIO(theBF, anExecutionContext, localTrace);

		//valueAssigned = matches(theBF, anExecutionContext, localTrace);
	}

	return valueAssigned;
}

/*
bool OfflineTestProcessor::matches(const BF & anElement,
		ExecutionContext & anExecutionContext, TraceSequence & localTrace)
{
	bool valueAssigned = false;
	if( anElement.is< AvmCode >() )
	{
		const AvmCode & theAC = anElement.to< AvmCode >();

		switch( theAC.getAvmOpCode() )
		{
			case AVM_OPCODE_PARALLEL :
			case AVM_OPCODE_SEQUENCE :
			{
				for( const auto & itOperand : theAC.getOperands() )
				{
					if( matchesIO( itOperand, anExecutionContext, localTrace) )
					{
						valueAssigned = true;
					}
					else
					{
						// Only for AVM_OPCODE_SEQUENCE
//						valueAssigned = false;
//						break;
					}
				}
				break;
			}

			default:
			{
				for( const auto & itOperand : theAC.getOperands() )
				{
					if( matchesIO( itOperand, anExecutionContext, localTrace) )
					{
						valueAssigned = true;
					}
				}
				break;
			}
		}
	}
	else if( anElement.is< ExecutionConfiguration >() )
	{
		valueAssigned = matchesIO(
				anElement.to< ExecutionConfiguration >(),
				anExecutionContext, localTrace);
	}

	return valueAssigned;
} */

bool OfflineTestProcessor::matchesIO(const BF & anElement,
		ExecutionContext & anExecutionContext, TraceSequence & localTrace)
{
	bool valueAssigned = false;
	if( anElement.is< AvmCode >() )
	{
		const AvmCode & theAC = anElement.to< AvmCode >();

		switch( theAC.getAvmOpCode() )
		{
			case AVM_OPCODE_PARALLEL :
			case AVM_OPCODE_SEQUENCE :
			{
				if( (mFoldingFlag && (mStepScheduler == AVM_OPCODE_INTERLEAVING))
					|| (theAC.getAvmOpCode() == AVM_OPCODE_PARALLEL) )
				{
					BFList listIO;
					listIO.append( theAC.getOperands() );

					for( auto itOperand = listIO.begin() ;
							itOperand != listIO.end() ;  )
					{
						// matchesIO remove conform prefix and continue analyze
						if( matchesIO(*itOperand, anExecutionContext, localTrace) )
						{
							valueAssigned = true;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "INTERLEAVE @ STEP => ERASE : " << itOperand->str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

							listIO.erase( itOperand );
							itOperand = listIO.begin();
						}
						else
						{
							++itOperand;
						}
					}

					for( const auto & itOperand : listIO )
					{
						if( hasObservableSignal(itOperand) )
						{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "INTERLEAVE @ STEP => UNOBSERVE EXPECTED : "
			<< itOperand.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

							return( false );
						}
					}
				}
				else
				{
					for( const auto & itOperand : theAC.getOperands() )
					{
						// matchesIO remove conform prefix and continue analyze
						if( matchesIO(itOperand, anExecutionContext, localTrace) )
						{
							valueAssigned = true;
						}
						else if( (theAC.getAvmOpCode() == AVM_OPCODE_SEQUENCE)
								&& hasObservableSignal(itOperand) )
						{
							// only for SEQUENCE
							valueAssigned = false;
							break;
						}
					}
				}
				break;
			}

			default:
			{
				for( const auto & itOperand : theAC.getOperands() )
				{
					if( matchesIO(itOperand, anExecutionContext, localTrace) )
					{
						valueAssigned = true;
					}
					else if( hasObservableSignal(itOperand) )
					{
						// only for SEQUENCE
						valueAssigned = false;
						break;
					}
				}
				break;
			}
		}
	}
	else if( anElement.is< ExecutionConfiguration >() )
	{
		valueAssigned = matchesIO( anElement.to< ExecutionConfiguration >(),
				anExecutionContext, localTrace);
	}

	return valueAssigned;
}


bool OfflineTestProcessor::matchesIO(
		const ExecutionConfiguration & anExecutionConfiguration,
		ExecutionContext & anExecutionContext, TraceSequence & localTrace)
{
	// TODO: here, the exec configuration is the main? one.
	// Maybe we will need to take into account cases where the input/outputs
	// are considered from a sub-machine point of view.
	bool valueAssigned = false;
	if( anExecutionConfiguration.isAvmCode() )
	{
		const BFCode & theAC = anExecutionConfiguration.getAvmCode();

		RuntimeID theRID = anExecutionConfiguration.getRuntimeID();


		AVM_OS_LOG << "OfflineTestProcessor::matchesIO < theAC > : "
				<< theAC.str() << std::endl;

		switch( theAC->getAvmOpCode() )
		{
			case AVM_OPCODE_INPUT :
			case AVM_OPCODE_OUTPUT :
			{
				if( theAC->first().is< InstanceOfPort >() )
				{
					const InstanceOfPort & aPort =
							theAC->first().to< InstanceOfPort >();
					const InstanceOfPort & ioPort = ( aPort.hasAliasTarget()
							? aPort.getAliasTarget()->as< InstanceOfPort >()
							: aPort );


					// the first item in the trace could be a delay,
					// (but it may happen that here are two consecutive actions)
					// (but there are never two consecutive time delays)
					// so we compare ports with the first and second entries in the localObs
					
					// we retrieve the next action in the localTrace
					// either it is in the first TracePoint
					// or the first TracePoint is a delay and so it must be the next one
					TracePoint * aTracePoint = nullptr;
					if( localTrace.points.nonempty() )
					{
						aTracePoint = localTrace.points.first().to_ptr< TracePoint >();
						if( aTracePoint->isTime() )
						{
							if( localTrace.points.populated() )
							{
								aTracePoint = localTrace.points.second().to_ptr< TracePoint >();
							}
							else
							{
								valueAssigned = lookupDelay(anExecutionContext, localTrace);
								break;
							}
						}
					}
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "OFFLINE TEST:: TracePoint considered: " << std::endl;
//	aTracePoint->toStream(AVM_OS_LOG << AVM_TAB_INDENT);
//	AVM_OS_LOG << "Compiled form name :" << ioPort.getQualifiedNameID() << std::endl
//		<<	"TracePoint object Id :" <<aTracePoint->object->getNameID() << std::endl
//		<< "TracePoint operator :" << aTracePoint->to_string(aTracePoint->op) << std::endl;
//	AVM_OS_LOG << END_INDENT << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )


					if( (aTracePoint != nullptr)
						&& aTracePoint->isCom(theAC->getAvmOpCode(),
								theAC->getOptimizedOpCode(), theRID, ioPort) )
//							&& (ioPort.getNameID() == aTracePoint->object->getNameID())
//							&& ((aTracePoint->op == AVM_OPCODE_OUTPUT)
//								|| (aTracePoint->op == AVM_OPCODE_OUTPUT_ENV)) )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST:: " << TracePoint::to_string(theAC->getAvmOpCode())
			<< " found on port: "   << ioPort.getQualifiedNameID() << std::endl
			<< "with machine : "    << ioPort.getRuntimeContainerRID().str() << std::endl
			<< "with machine 2 : "  << anExecutionConfiguration.getRuntimeID().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

						valueAssigned = lookupValue(theAC, anExecutionContext,
								anExecutionConfiguration, ioPort,
								theAC->getAvmOpCode(), localTrace);
						break;
					}

					const ExecutionData & anED = anExecutionContext.getExecutionData();

					const RoutingData & ioRD = AvmCommunicationFactory::
						searchRoutingData(anED, theAC->getAvmOpCode(), ioPort, theRID);

					if( ioRD.valid() )
					{
						if( ioRD.getProtocol() == ComProtocol::PROTOCOL_ENVIRONMENT_KIND  )
						{
							// we retrieve the next action in the localTrace
							// either it is in the first TracePoint
							// or the first TracePoint is a delay and so it must be the next one
							TracePoint * aTracePoint = nullptr;
							if( localTrace.points.nonempty() )
							{
								aTracePoint = localTrace.points.first().to_ptr< TracePoint >();
								if( aTracePoint->isTime() && localTrace.points.populated() )
								{
									aTracePoint = localTrace.points.second().to_ptr< TracePoint >();
								}
							}

							if( (aTracePoint != nullptr)
								&& aTracePoint->isCom(theAC->getAvmOpCode(),
										theAC->getOptimizedOpCode(), theRID, ioPort) )
//								&& (ioPort.getNameID() == aTracePoint->object->getNameID())
//								&& ((aTracePoint->op == AVM_OPCODE_OUTPUT)
//									|| (aTracePoint->op == AVM_OPCODE_OUTPUT_ENV)) )
							{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST:: " << TracePoint::to_string(theAC->getAvmOpCode())
			<< " to/from environment on port: " << ioPort.getQualifiedNameID() << std::endl
			<< "with machine : " << ioPort.getRuntimeContainerRID().str() << std::endl
			<< "with machine 2 : " << anExecutionConfiguration.getRuntimeID().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

								valueAssigned = lookupValue(theAC,
										anExecutionContext, anExecutionConfiguration,
										ioPort, theAC->getAvmOpCode(), localTrace);
							}
						}
					}
				}

				break;
			}

			case AVM_OPCODE_ASSIGN_NEWFRESH :
			{
				valueAssigned = false;
				break;
			}


			default :
			{
				valueAssigned = false;

				// Pas de récursion car anExecutionConfiguration est atomique du point de vue la I/O-Trace
//				for( const auto & itOperand : theAC->getOperands() )
//				{
//					if( matchesIO( itOperand, anExecutionContext, localTrace) )
//					{
//						valueAssigned = true;
//					}
//				}
				break;
			}
		}
	}

	return valueAssigned;
}

bool OfflineTestProcessor::updateTime(TracePoint * aTracePoint,
		ExecutionContext & anExecutionContext, TraceSequence * localTrace)
{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Time passing... add time constraint, input" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	const BF & currentTimeVar = ENV.getRvalue(
			anExecutionContext.getwExecutionData(),
			anExecutionContext.getExecutionData().getSystemRID(),
			(* timeReferenceInstance));

	// assign the delay to the difference of currtime - ref time
	BF buildValue = ENV.getBuilder().build(
			theMainExecutionData, aTracePoint->val(0));

	OfflineTestProcessorInfo * currentOfflineTestInfo =
			anExecutionContext.getUniqInformation()
			->getUniqSpecificInfo< OfflineTestProcessorInfo >();

	// TOD DO Optimization
//	BF localTimedCondition =
	anExecutionContext.getwExecutionData().mwsetPathTimedCondition(
			ExpressionConstructor::andExpr(
			anExecutionContext.getExecutionData().getPathTimedCondition(),
			ExpressionConstructor::eqExpr(
				ExpressionConstructor::minusExpr(currentTimeVar,
				currentOfflineTestInfo->getTimeReference()),
				buildValue)) );

	if( SolverFactory::isSatisfiable(theSolverKind, //localTimedCondition) )
			anExecutionContext.getExecutionData().getPathTimedCondition()) )
	{
		currentOfflineTestInfo->addTimeElapsingDelta(buildValue);

		if( not ENV.setRvalue(anExecutionContext.getwExecutionData(),
				anExecutionContext.getExecutionData().getSystemRID(),
				(* timeReferenceInstance),
				currentOfflineTestInfo->getTimeElapsing()) )
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "setRvalue:> " << timeReferenceInstance->getQualifiedNameID()
					<< " <-- " << currentOfflineTestInfo->getTimeElapsing()
					<< SEND_EXIT;
		}
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
AVM_OS_LOG << "3. FAIL: path constraint not satisfiable (delay)" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return false;
	}

	// remove read val
	localTrace->points.remove_first();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "And the timed ( $time: " << currentTimeVar.str()
			<< " ) constraint is "
			<< anExecutionContext.getExecutionData().getPathTimedCondition().str()
			<< std::endl
			<< "With time reference : "
			<< currentOfflineTestInfo->getTimeReference().str() << std::endl
			<< "With time elapsing : "
			<< currentOfflineTestInfo->getTimeElapsing().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	return true;
}



bool OfflineTestProcessor::lookupValue(
		AvmCode * anAC, ExecutionContext & anExecutionContext,
		const ExecutionConfiguration & anExecutionConfiguration,
		const InstanceOfPort & aPort, AVM_OPCODE avmOpcode,
		TraceSequence & localTrace)
{
	// assign the respective value (if found) to its respective variable

	bool valueAssigned = false;
	TracePoint * aTracePoint = nullptr;

	while( true )
	{

		std::size_t nbParam = aPort.getParameterCount();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Number of parameters:" << nbParam <<  std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		aTracePoint = localTrace.points.first().to_ptr< TracePoint >();

		// considering communication actions
//TODO: consider other observable actions (such as variable assignations) ?
		if( (avmOpcode == AVM_OPCODE_OUTPUT)
			|| (avmOpcode == AVM_OPCODE_INPUT) )
		{
			// compare action in tree with local obs: one or two steps
			// 1. (conditional) : if the first value is a time var:
			// assign the time to the data var
			// and delete the trace point from the trace
			// 2. compare action with trace element

			if( aTracePoint->isTime() &&
				( (theTimeVarInstance == aTracePoint->object) /*||
				(theTimeVarInstance->getNameID() == aTracePoint->object->getNameID())*/ ) )
			{
				// 1. case where first value is a time var
				valueAssigned = updateTime(aTracePoint,
						anExecutionContext, &localTrace);
				if( not valueAssigned)
				{
					break;
				}

				// Trace coverage for reporting
				theTraceCoverageBitSet[aTracePoint->tpid] = true;

				//localTrace.points.remove_first();
			}

			// Step 2 : compare action in symbolic tree with trace element
			//now reading what should be a signal
			aTracePoint = localTrace.points.first().to_ptr< TracePoint >();
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "The port in the trace is " << aTracePoint->object->str() << std::endl
	<< "And the port is " << aPort.getNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )

			// now reading values to be compared

			// the signal should correspond with the value in
			// the trace, else it is simply not removed
			if( aTracePoint->object == (& aPort) )
			{
				//checking direction of signal
				if(  (avmOpcode == AVM_OPCODE_OUTPUT) &&
					((aTracePoint->op == AVM_OPCODE_INPUT) ||
					(aTracePoint->op == AVM_OPCODE_INPUT_ENV)) )
				{
					AVM_OS_LOG << "OFFLINE TEST: WARNING! input when expecting output!"
								<< std::endl;
					valueAssigned = false;
					break;
				}
				if( (avmOpcode == AVM_OPCODE_INPUT) &&
					((aTracePoint->op == AVM_OPCODE_OUTPUT) ||
					(aTracePoint->op == AVM_OPCODE_OUTPUT_ENV)) )
				{
					AVM_OS_LOG << "OFFLINE TEST: WARNING! output when expecting input!"
								<< std::endl;
					valueAssigned = false;
					break;
				}


				//each of the parameters must match
				bool matchingParams = true;
				RuntimeQuery RQuery( getConfiguration() );

				for( std::size_t i = 0 ; matchingParams && (i < nbParam) ; ++i )
				{
					if( anAC->operand(i+1).is< InstanceOfData >() )
					{
						BF foundVar = RQuery.searchVariable(
								anExecutionContext.getExecutionData(),
								anExecutionConfiguration.getRuntimeID(),
								anAC->operand(i+1) );

						if( foundVar.valid() )
						{
							matchingParams = assignValue(
									anAC, anExecutionContext,
									foundVar, aTracePoint, i );
						}
						else
						{
							AVM_OS_LOG << "lookupValue(...): "
										"Unfound symbolic parameter :> "
										<< anAC->operand(i+1) << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "cufi: " << anAC->operand(i+1).to< InstanceOfData >().getAstFullyQualifiedNameID() << std::endl
				<< "port: " << str_header( aPort ) << std::endl
				<< "rid : " << str_header( anExecutionConfiguration.getRuntimeID() ) << std::endl
				<< "com : " << str_header( anExecutionConfiguration.getRuntimeID().getCommunicator(aPort) ) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
							}
					}
					else
					{
						matchingParams = assignValue(
								anAC, anExecutionContext,
								BF::REF_NULL, aTracePoint, i );
					}

					/*
					if( anAC->operand(i+1).is< InstanceOfData >() )
					{
						valueAssigned = assignValue(anAC, anExecutionContext,
								aTracePoint, i);

					}

					else
//						if( anAC->operand(i+1).isNumber()
//							|| anAC->operand(i+1).isBoolean()
//							|| anAC->operand(i+1).isBuiltinString()
//							|| anAC->operand(i+1).isEnumSymbol())
					//TODO: check whether this is not problematic (certain types, machine, etc)
					{
						matchingParams = ((aTracePoint->val(i) == anAC->operand(i+1)) && matchingParams);
					}
					*/
				}

				if( matchingParams )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: com action corresponds to trace, delete it if value assigned is satisfiable" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					// Trace coverage for reporting
					theTraceCoverageBitSet[aTracePoint->tpid] = true;

					localTrace.points.remove_first();

					valueAssigned = true;
				}

				else
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: WARNING: com action : " ;
	for( std::size_t i = 0 ; i < nbParam; ++i )
	{
		AVM_OS_LOG << " " << anAC->operand(i+1).str() ;
	}
	//aPort->getParameter(0)
	AVM_OS_LOG	<< " does not correspond to trace : "
			<< aTracePoint->value.str()
			<< " , do not delete it (but deleting for the moment)"
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					valueAssigned = false;
					anExecutionContext.getwExecutionData().
							mwsetPathCondition( ExpressionConstant::BOOLEAN_FALSE );
				}
				break;
			}
		}
		/*
		//Now, treat case where local obs is an input
		else if( avmOpcode == AVM_OPCODE_INPUT )
		{
			// check input in tree with local obs: on or two steps
			// 1. if first element in trace is a time var
			// assign time data and move on
			// 2. compare element in trace against input
			if( aTracePoint->isTime() &&
				(theTimeVarInstance->getNameID() == aTracePoint->object->getNameID()) )
			{
				valueAssigned = updateTime(aTracePoint, anExecutionContext, &localTrace);
				if( valueAssigned ==  false )
				{
					break;
				}

				// Trace coverage for reporting
				theTraceCoverageBitSet[aTracePoint->tpid] = true;

				localTrace.points.remove_first();
			}

			//now reading what should be a signal
			aTracePoint = localTrace.points.first().to_ptr< TracePoint >();

//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "The port in the trace is " << aTracePoint->object->str() << std::endl
//	<< "And the port is " << aPort->getNameID()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			// now reading input value to be compared
			if( aTracePoint->object->getNameID() ==  aPort->getNameID() )
			{

				if( (aTracePoint->op == AVM_OPCODE_OUTPUT) ||
					(aTracePoint->op == AVM_OPCODE_OUTPUT_ENV) )
				{
					AVM_OS_LOG << "OFFLINE TEST: WARNING! output when expecting input!"
								<< std::endl;
					valueAssigned = false;
					break;
				}
				// the input should correspond with the value in
				// the trace, else it is simply not removed

				bool matchingParams = (aTracePoint->valCount() == nbParam);

				if( matchingParams )
				{
					for( std::size_t i = 0 ; matchingParams && (i < nbParam) ; ++i )
					{
						//TODO: add conditional numeric/symbolic
						if( anAC->operand(i+1).is< InstanceOfData >() )
						{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assigning value: " << aTracePoint->val(i) <<  "to variable: "
			<< anAC->operand(i+1).to< InstanceOfData >().getNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

							valueAssigned = assignValue(anAC,
									anExecutionContext, aTracePoint, i);

						}

						else if( anAC->operand(i+1).isNumber()
								|| anAC->operand(i+1).isBoolean()
								|| anAC->operand(i+1).isBuiltinString()
								|| anAC->operand(i+1).isEnumSymbol() )
						{
							matchingParams = ((aTracePoint->val(i) ==
									anAC->operand(i+1)) && matchingParams);
						}
						else
						{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Unexpected Kind: " << anAC->operand(i+1).classKindName() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

							break;
						}
					}

					if( matchingParams)
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: output corresponds to trace, delete it" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )


						// Trace coverage for reporting
						theTraceCoverageBitSet[aTracePoint->tpid] = true;

						localTrace.points.remove_first();
						valueAssigned = true;
					}
					else
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: WARNING: input : " ;
	for( std::size_t i = 0 ; i < nbParam; ++i )
	{
		AVM_OS_LOG << "\t" << anAC->operand(i+1).str() ;
	}
	//aPort->getParameter(0)
	AVM_OS_LOG	<< " does not correspond to trace : "
			<< aTracePoint->value.str()
			<< " , do not delete it (but deleting for the moment)" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

						valueAssigned = false;

//
 // TODO Modification de la path condition sans risque dans le smart pointer ExecutionData
 //
//						if( not PathConditionProcessor::addPathCondition(
//							anExecutionContext.getExecutionData(),
//							ExpressionConstant::BOOLEAN_FALSE) )
//						{
//							//!! INSATISFIABLE PATH CONDITION
//						}

						anExecutionContext.getExecutionData().
								mwsetPathCondition( ExpressionConstant::BOOLEAN_FALSE );
					}
				}
				else
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: WARNING : number of parameters expected" << nbParam
			<< "while actual number of parameters given in the trace is"
			<< aTracePoint->valCount() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
				}
				break;
			}
		}
		break;*/
	}

	if( valueAssigned )
	{
		// Sometimes, the constraint is no longer valid, but it still appears
		// in the graph

		if( SolverFactory::isSatisfiable(theSolverKind,
				anExecutionContext.getExecutionData().getPathCondition()) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			AVM_OS_LOG << "The constraint is satisfied !" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
		else
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Warning! the path constraint after assigning the values is false !"
		<< "\n\t==> returning false, so the EC children won't be evaluated anymore !"
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			theTraceCoverageBitSet[aTracePoint->tpid] = false;

			valueAssigned = false;
		}
	}

	return valueAssigned;
}













bool OfflineTestProcessor::lookupDelay(
		ExecutionContext & anExecutionContext, TraceSequence & localTrace)
{
	// assign the respective value (if found) to its respective variable

	bool valueAssigned = false;

	TracePoint * aTracePoint = localTrace.points.first().to_ptr< TracePoint >();

	if( aTracePoint->isTime() &&
		(theTimeVarInstance == aTracePoint->object) )
	{
		// 1. case where first value is a time var
		valueAssigned = updateTime(aTracePoint, anExecutionContext, &localTrace);
		if( valueAssigned)
		{
			// Trace coverage for reporting
			theTraceCoverageBitSet[aTracePoint->tpid] = true;
		}
	}

	return valueAssigned;
}




















bool OfflineTestProcessor::assignValue(AvmCode * anAC,
		ExecutionContext & anExecutionContext,
		const ExecutionConfiguration & anExecutionConfiguration,
		InstanceOfPort * aPort,
		TraceSequence & localTrace, int offset)
{
	// look for the respective value:
	// simple search on the vector of pair of values until we find
	// a match on the variable name; if found, "assign" the value...
	// The value is assigned as a constraint in the Path Condition
	TracePoint * aTracePoint = localTrace.points.first().to_ptr<TracePoint>();
	if( aTracePoint->isTime() &&
		( (theTimeVarInstance == aTracePoint->object) /*||
		(theTimeVarInstance->getNameID() == aTracePoint->object->getNameID())*/ ) )
	{
		// since the traces are of the form DELAY.ACTION, and since we may have consecutive
		// inputs/outputs without delays in between (structures of data),
		// if we are in such a case (a trace of the form 5.a?.a?), we verify that
		// the FIRST item in the trace is a delay, and that the SECOND one is the input/output
		// that we are expecting to see.
		// This happens only once, since for the case when the trace is just a?
		// (and 5.a? have been read), we compare directly with the FIRST item
		// of the trace

		// TODO: change this to take outputs into account (next step)
		// if there is a passage of time observation, just add it
		// to the path condition of the node (EC)
		// emit verdicts according to output
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assign value: Time passing... add time constraint" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		const BF & currentTimeVar = ENV.getRvalue(
				anExecutionContext.getwExecutionData(),
				anExecutionContext.getExecutionData().getSystemRID(),
				(* timeReferenceInstance));

		// assign the delay to the difference of currtime - ref time
		BF buildValue = ENV.getBuilder().build(
				theMainExecutionData, aTracePoint->val(0));

		anExecutionContext.getUniqInformation()
				->getUniqSpecificInfo< OfflineTestProcessorInfo >()
				->addTimeElapsingDelta(buildValue);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "the vars are: curr timevar: "
			<< currentTimeVar.str() << std::endl
			<< "reference time:> " << std::endl
			<< "\tvar   : " << anExecutionContext.getUniqInformation()
			->getUniqSpecificInfo< OfflineTestProcessorInfo >()
			->getTimeReference().str()
			<< std::endl
			<< "\tvalue : " << buildValue.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		anExecutionContext.getwExecutionData().mwsetPathTimedCondition(
			ExpressionConstructor::andExpr(
				anExecutionContext.getExecutionData().getPathTimedCondition(),
				ExpressionConstructor::eqExpr(
					ExpressionConstructor::minusExpr(currentTimeVar,
						anExecutionContext.getUniqInformation()
						->getUniqSpecificInfo< OfflineTestProcessorInfo >()
						->getTimeReference()),
					buildValue)));

		if( not SolverFactory::isSatisfiable(theSolverKind,
			anExecutionContext.getExecutionData().getPathTimedCondition()) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			AVM_OS_LOG << "4. FAIL: path constraint not satisfiable due to delay"
					<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			return false;
		}

		// Trace coverage for reporting
		theTraceCoverageBitSet[aTracePoint->tpid] = true;

		localTrace.points.remove_first();
		aTracePoint = localTrace.points.first().to_ptr<TracePoint>();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "And the second timed constraint is "
			<< anExecutionContext.getExecutionData().getPathTimedCondition().str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	}

	// everything is OK if the first value in the trace to be read corresponds
	// to the one that we are looking for, else???
	std::size_t nbParam = aPort->getParameterCount();

	if( (aTracePoint->object ==  aPort) &&
		(nbParam == aTracePoint->valCount()) )
	{
		//int nbParam = aPort->getParameterCount();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Found in its place, variable: ";
	for( std::size_t i = 0 ; i < nbParam ; ++i )
	{
		AVM_OS_LOG	<< "\t" << anAC->operand(i+1).to< InstanceOfData >().getFullyQualifiedNameID();
	}
	AVM_OS_LOG	<< " in port " << aPort->getNameID()
		<< " == " << aTracePoint->object->str() << std::endl
		<< "with machine 3 : " << aPort->getRuntimeContainerRID().getNameID() << std::endl
		<< "with machine 4 : " << anExecutionConfiguration.getRuntimeID().getNameID() << std::endl
		<< "with machine 5 : " << anExecutionConfiguration.getRuntimeID().
				getCommunicator(*aPort).getNameID() << std::endl
		<< "About to assign value:> " << aTracePoint->value.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		RuntimeQuery RQuery( getConfiguration() );

		for( std::size_t i = 0 ; i < nbParam ; ++i )
		{
			// the value is stored in the trace point and accessed through the val method
			BF buildValue = ENV.getBuilder().build(
					theMainExecutionData, aTracePoint->val(i));

	//TODO: check whether there is no issue with the management of strings
			if( aTracePoint->val(i).isBuiltinString() )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assigning a string ! " << aTracePoint->val(i).str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}
			else
			{
				// TODO : tests
				if( not PathConditionProcessor::addPathCondition(
					anExecutionContext.getwExecutionData(),
					ExpressionConstructor::eqExpr(anAC->operand(i+1), buildValue),
					false) )
				{
					//!! INSATISFIABLE PATH CONDITION
					return false; // ??? TODO

				}
			}

			BF variableInstance = RQuery.searchVariable(
					anExecutionContext.getExecutionData(),
					anExecutionConfiguration.getRuntimeID(), anAC->operand(i+1) );

			if( variableInstance.valid() )
			{
				// Assign the value
				ENV.setRvalue(anExecutionContext.getwExecutionData(),
					variableInstance.to< InstanceOfData >(), buildValue);
			}
			else
			{
				AVM_OS_LOG << "assignValue(...): Unfound symbolic parameter :> "
							<< anAC->operand(i+1) << std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
AVM_OS_LOG << "cufi: "
	<< anAC->operand(i+1).to< InstanceOfData >().getAstFullyQualifiedNameID() << std::endl
	<< "port: " << str_header( aPort ) << std::endl
	<< "rid : " << str_header( anExecutionConfiguration.getRuntimeID() ) << std::endl
	<< "com : " << str_header( anExecutionConfiguration.getRuntimeID().getCommunicator(*aPort) )
	<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}
		}

		// Trace coverage for reporting
		theTraceCoverageBitSet[aTracePoint->tpid] = true;

		localTrace.points.remove_first();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "After observing the local obs trace of size: "
			<< localTrace.points.size() << std::endl;
	printTrace(localTrace);

	AVM_OS_LOG << "And the all constraint is :>\n\t"
				<< anExecutionContext.getExecutionData().getAllPathCondition().str()
				<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return true;
	}
	else if( nbParam != aTracePoint->valCount() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OFFLINE TEST: WARNING : number of parameters expected" << nbParam
			<< "while actual number of parameters given in the trace is"
			<< aTracePoint->valCount() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}
	else
	{

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Input/Output not expected ("
			<< anAC->operand(1).to< InstanceOfData >().getAstFullyQualifiedNameID()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}

	return false;
}



bool OfflineTestProcessor::assignValue(
		AvmCode * anAC, ExecutionContext & anExecutionContext,
		const BF & variableInstance, TracePoint * aTracePoint, int paramNb)
{

	bool valueAssigned =false;
	// the value is stored in the trace point and accessed through the val method

	if(anAC->operand(paramNb+1).isBuiltinString())
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Checking string equality! "
		<< anAC->operand(paramNb+1).str()
		<< " =? "
		<< aTracePoint->val(paramNb).str()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		valueAssigned = (aTracePoint->val(paramNb) == anAC->operand(paramNb+1));
	}

	else if(anAC->operand(paramNb+1).isIdentifier())
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
AVM_OS_LOG << "Checking that identifiers match: "
		<< anAC->operand(paramNb+1).str()
		<< " =? "
		<< aTracePoint->val(paramNb).str()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		valueAssigned =
				(aTracePoint->val(paramNb).to< Identifier >().getValue()
				== anAC->operand(paramNb+1).to< Identifier >().getValue());
	}

	//gestion du type machine
	else if( anAC->operand(paramNb+1).is< RuntimeID >() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
AVM_OS_LOG << "Checking machine equality: "
		<< anAC->operand(paramNb+1).str()
		<< " =? "
		<< aTracePoint->val(paramNb).str()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		RuntimeID machine = anAC->operand(paramNb+1).as_bf< RuntimeID >();
		valueAssigned = (aTracePoint->val(paramNb).isTEQ(machine.getInstance()));
	}


	// Const value
	// TODO : testing equality between value in trace and at runtime properly
	/*
	else if( anAC->operand(paramNb+1).isConstValue() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
AVM_OS_LOG << "Checking parameter equality: "
		<< anAC->operand(paramNb+1).str()
		<< " =? "
		<< aTracePoint->val(paramNb).str()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		valueAssigned = (aTracePoint->val(paramNb).isEQ(anAC->operand(paramNb+1)));
	}*/

	// Symbolic execution Value
	else if( aTracePoint->hasValue() )
	{
		BF buildValue = ENV.getBuilder().build(
				theMainExecutionData, aTracePoint->val(paramNb));

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assigning value: " << aTracePoint->val(paramNb)
		<< " to variable: " << anAC->operand(paramNb+1).str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		//TODO: check whether there is no issue with the management of strings
		if( aTracePoint->val(paramNb).isBuiltinString() )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assigning a string ! "
		<< aTracePoint->val(paramNb).str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
		else {
			if( not PathConditionProcessor::addPathCondition(
				anExecutionContext.getwExecutionData(),
				ExpressionConstructor::eqExpr(anAC->operand(paramNb+1), buildValue),
				false ) )
				//TODO : testing whether adding parameter false is better
			{
				//!! INSATISFIABLE PATH CONDITION
				return false; // ??? TODO
			}
		}

		return true;
	}
	else
	{
		//!! UNFOUND PARAMS
		AVM_OS_LOG << "Assigning value: ERROR ! Trace point without parameter's value"
				<< aTracePoint->toString() << std::endl;

		return false;
	}

	return valueAssigned;
}


//bool OfflineTestProcessor::assignValue(AvmCode * anAC,
//		ExecutionContext & anExecutionContext,
//		const ExecutionConfiguration & anExecutionConfiguration,
//		BF dataVar, const InstanceOfPort * aPort,
//		TraceSequence & localTrace, int offset)
//{
//	// look for the respective value:
//	// simple search on the vector of pair of values until we find
//	// a match on the variable name; if found, "assign" the value...
//	// The value is assigned as a constraint in the Path Condition
//	TracePoint * aTracePoint = localTrace.points.first().to_ptr<TracePoint>();
//	if( aTracePoint->isTime() &&
//		(theTimeVarInstance->getNameID() == aTracePoint->object->getNameID()) )
//	{
//		// since the traces are of the form DELAY.ACTION, and since we may have consecutive
//		// inputs/outputs without delays in between (structures of data),
//		// if we are in such a case (a trace of the form 5.a?.a?), we verify that
//		// the FIRST item in the trace is a delay, and that the SECOND one is the input/output
//		// that we are expecting to see.
//		// This happens only once, since for the case when the trace is just a?
//		// (and 5.a? have been read), we compare directly with the FIRST item
//		// of the trace
//
//		// TODO: change this to take outputs into account (next step)
//		// if there is a passage of time observation, just add it
//		// to the path condition of the node (EC)
//		// emit verdicts according to output
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "Assign value: Time passing... add time constraint" << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//
//		const BF & currentTimeVar = ENV.getRvalue(
//				anExecutionContext.getExecutionData(),
//				anExecutionContext.getExecutionData().getSystemRID(),
//				timeReferenceInstance);
//
//		// assign the delay to the difference of currtime - ref time
//		BF buildValue = ENV.getBuilder().build(
//				theMainExecutionData, aTracePoint->val(0));
//
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "the vars are: curr timevar: "
//			<< currentTimeVar.str() << std::endl
//			<< "reference time:> " << std::endl
//			<< "\tvar   : " << anExecutionContext.getUniqInformation()
//			->getUniqSpecificInfo< OfflineTestProcessorInfo >()
//			->getTimeReference().str() << std::endl
//			<< "\tvalue : " << buildValue.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//
//		anExecutionContext.getExecutionData().mwsetPathTimedCondition(
//			ExpressionConstructor::andExpr(
//				anExecutionContext.getExecutionData().getPathTimedCondition(),
//					ExpressionConstructor::eqExpr(
//						ExpressionConstructor::minusExpr(currentTimeVar,
//							anExecutionContext.getUniqInformation()
//							->getUniqSpecificInfo< OfflineTestProcessorInfo >()
//							->getTimeReference()),
//						buildValue)));
//
//		if( not SolverFactory::isSatisfiable(theSolverKind,
//			anExecutionContext.getExecutionData().getPathTimedCondition()) )
//		{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//			AVM_OS_LOG << "4. FAIL: path constraint not satisfiable due to delay"
//					<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//			return false;
//		}
//
// 		// Trace coverage for reporting
//		theTraceCoverageBitSet[aTracePoint->tpid] = true;
//
//		localTrace.points.remove_first();
//		aTracePoint = localTrace.points.first().to_ptr<TracePoint>();
//
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "And the second timed constraint is "
//			<< anExecutionContext.getExecutionData().getPathTimedCondition().str()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	}
//
//	// everything is OK if the first value in the trace to be read corresponds
//	// to the one that we are looking for, else???
//
//	if( aTracePoint->object->getNameID() ==  aPort->getNameID() )
//	{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "Found in its place, variable: "
//		<< dataVar.to< InstanceOfData >().getFullyQualifiedNameID()
//		<< " in port " << aPort->getNameID()
//		<< " == " << aTracePoint->object->str() << std::endl
//		<< "with machine 3 : " << aPort->getRuntimeContainerRID().getNameID() << std::endl
//		<< "with machine 4 : " << anExecutionConfiguration.getRuntimeID().getNameID() << std::endl
//		<< "with machine 5 : " << anExecutionConfiguration.getRuntimeID().
//				getCommunicator(aPort).getNameID() << std::endl
//		<< "About to assign value:> " << aTracePoint->val(0).str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//
//		// for the moment, the value is stored in the third position of the list
//		// the value is stored in the trace point and accessed through the val method
//		BF buildValue = ENV.getBuilder().build(
//				theMainExecutionData, aTracePoint->val(0));
//
////TODO: check whether there is no issue with the management of strings
//		if( aTracePoint->val(0).isBuiltinString() )
//		{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "Assigning a string ! "
//			//<<dataVar.to< InstanceOfData >().getAstFullyQualifiedNameID() << std::endl
//			//<< aTracePoint->val(0).str()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//		}
//		else {
//			anExecutionContext.getExecutionData().mwsetPathCondition(
//				ExpressionConstructor::andExpr(
//					anExecutionContext.getExecutionData().getPathCondition(),
//					ExpressionConstructor::eqExpr(dataVar, buildValue)));
//		}
//
//		BF variableInstance = ENV.getBuilder().searchSymbolData(
//				theMainExecutionData, dataVar->getAstFullyQualifiedNameID());
//
//		// Assign the value
//		ENV.setRvalue(anExecutionContext.getExecutionData(),
//				variableInstance, buildValue);
//
// 		// Trace coverage for reporting
//		theTraceCoverageBitSet[aTracePoint->tpid] = true;
//
//		localTrace.points.remove_first();
//
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "After observing the local obs trace of size: "
//			<< localTrace.points.size() << std::endl;
//	printTrace(localTrace);
//
//	AVM_OS_LOG << "And the all constraint is :>\n\t"
//			<< anExecutionContext.getExecutionData().getAllPathCondition().str()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//
//		return true;
//	}
//	else
//	{
//
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "Input/Output not expected (" <<
//			dataVar.to< InstanceOfData >().getAstFullyQualifiedNameID()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	}
//
//	return false;
//}

/*bool OfflineTestProcessor::reAssignValue(AvmCode * anAC,
//		ExecutionContext & anExecutionContext,
//		BF aValue, const InstanceOfPort * aPort,
//		VectorOfPairOfVariableValue * aTable, int offset)
//{
// This version of the method is for changing the value
// "associated" with port aPort


	TripleOfPortVariableOffset aTuple;

	VectorOfPairOfVariableValue::iterator it = aTable->begin();
	VectorOfPairOfVariableValue::iterator itend = aTable->end();

	// loop iterating on the vector of variable/values (parameters file)
	for( ; it != itend ; ++it)
	{
		// loop iterating on the vector of modified variables
		for (size_t i=0 ; i < theVectorOfPortVariableOffset.size() ; ++i )
		{
			aTuple = theVectorOfPortVariableOffset[i];
			if( aPort != aTuple.get<0>().to_ptr< InstanceOfPort >() )
			{
				continue;
			}
			AVM_OS_LOG << "search mapping " << std::endl;

			if( operator==(aTuple, std::make_tuple(
					aPort,(*it).first().to_ptr< InstanceOfData >(), offset)) )
			{
				AVM_OS_LOG << "mapping found!!! "
						<< aTuple.get<0>().to< InstanceOfPort >().getFullyQualifiedNameID()
						<< "," << aTuple.get<1>().to_ptr< InstanceOfData >().str()
						<< "," << aTuple.get<2>() << " con " << aPort->str()
						<< "," << (*it).first()->to_ptr< InstanceOfData >()->str()
						<< "," << offset << std::endl;

				// Create a new simbolic var and assign the constraint


				AVM_OS_LOG << "viendo ahora la symbolic var... para  "
						<< (*it).first()->getAstFullyQualifiedNameID() << std::endl
						<< "viendo ahora la symbolic var... para  "
						<< (*it).first()->getAstNameID() << std::endl;

				InstanceOfMachine * theMainSpecification =
					getConfiguration().getExecutableSystem().getSystemInstance();
				if( theMainSpecification != nullptr )
				{
					AVM_OS_LOG << "al menos no es null \n";
				}
				Variable * aVar = theMainSpecification->refExecutable().
					getAstMachine()->getVariable( (*it).first()->getAstNameID() );
				const BF & ripvalue = ENV.getRvalue(anExecutionContext.getExecutionData(),
					anExecutionContext.getExecutionData().getRuntimeID(theMainSpecification),
						(*it).first().to_ptr< InstanceOfData >());
				if( aVar != nullptr )
				{
					InstanceOfData * varGlobalTime = theMainSpecification->
							refExecutable().getAllVariables().rawByCompiled(aVar);
					AVM_OS_LOG << "VEMOSNOOOSSSS.........; "
							<< varGlobalTime->getFullyQualifiedNameID() << std::endl;
					const BF & rvalue = ENV.getRvalue(anExecutionContext.getExecutionData(),
						anExecutionContext.getExecutionData().getRuntimeID(theMainSpecification),
						varGlobalTime);
					AVM_OS_LOG << "VEMOSNOs MAS : " << rvalue.str();
				}
				if( ripvalue.valid() )
				{
					AVM_OS_LOG << "prvobemos a ver : " << ripvalue.str() << std::endl;
				}
				AVM_OS_LOG << "ES NULLLL \n";
				// tuple found, replace with new value
				BF buildValue = ENV.getBuilder().build(theMainExecutionData, aValue);
				ENV.setRvalue(anExecutionContext.getExecutionData(),
						(*it).first(), buildValue);
				return true;
			}
		}
	}
	//	return false;
	//}
	 */


bool OfflineTestProcessor::prefilter()
{
//	ExecutionContext & delEC = nullptr;

	ecQueue = &( getExecutionQueue().getReadyQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << std::endl << std::endl << "Working with EC: "
			<< (*ecQueueIt)->str_min() << " IO Trace: "
			<< (*ecQueueIt)->getIOElementTrace();
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		if( not prefilter(* (*ecQueueIt)) )
		{
			AVM_OS_LOG << "OfflineTestProcessor::Prefilter won't continue here!"
					<< std::endl;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Erasing EC: " << (*ecQueueIt)->str_min() << std::endl
			<< "\tIt's the " << (++theErasedNodes)
			<< "'nth EC that has been deleted !" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

//			delEC = (*it);

			ecQueueIt = ecQueue->erase(ecQueueIt);

//			AbstractProcessorUnit::remove(delEC ,
//					AVM_OS_LOG, "OfflineTestProcessor::remove");
		}
		else
		{
			ecQueueIt++;
		}
	}
	return (getExecutionQueue().hasReady());
}


bool OfflineTestProcessor::portInObsSignals(
		const RuntimeID & runtimeCtx, const InstanceOfPort & port,
		AVM_OPCODE ioOpcodeFamily, AVM_OPCODE ioOpcodeSpecific)
{
	for( const auto & itPoint : theObsSignals.points )
	{
		if( itPoint.is< TracePoint >() )
		{
			const TracePoint & aTracePoint = itPoint.to< TracePoint >();

//			if( aTracePoint.object == port )
			if( aTracePoint.isCom(ioOpcodeFamily,
					ioOpcodeSpecific, runtimeCtx, port) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Found, port in machine: " << aTracePoint.toString() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				return true;
			}
			else
			{
AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
	AVM_OS_LOG << "NOT Found, port in machine (from tree): "
			<< runtimeCtx.getQualifiedNameID() << " -> "
			<< TracePoint::to_string(ioOpcodeSpecific)
			<< " port " << port.getQualifiedNameID() << std::endl;
	AVM_OS_LOG << "NOT Found, comparing with (from obs signals): "
			<< aTracePoint.toString() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PROCESSOR )
			}
		}
	}

	return false;
}

bool OfflineTestProcessor::portInCtrlSignals(const TracePoint & portTP)
{
	return( theTraceFilter.pass(portTP) );
}

bool OfflineTestProcessor::hasObservableSignal(const BF & anElement)
{
	if( anElement.invalid() )
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "OfflineTestProcessor::hasObservableSignal:> "
			"Invalid Trace, returning false !" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return (false);
	}
	else if( anElement.is< AvmCode >() )
	{
		for( const auto & itOperand : anElement.to< AvmCode >().getOperands() )
		{
			if( hasObservableSignal( itOperand) )
			{
				return true;
			}
		}

	}
	else if( anElement.is< ExecutionConfiguration >() )
	{
		return( hasObservableSignal(
				anElement.to< ExecutionConfiguration >().getCode(),
				anElement.to< ExecutionConfiguration >()) );
	}

	return false;
}

bool OfflineTestProcessor::hasObservableSignal(
		const BF & anElement, const ExecutionConfiguration & anExexConf)
{
	if( anElement.invalid() )
	{
		return (false);
	}
	else if( anElement.is< AvmCode >() )
	{
		const AvmCode & theAC = anElement.to< AvmCode >();

AVM_IF_DEBUG_LEVEL_FLAG( HIGH , PRE_FILTERING )
	AVM_OS_LOG << "Analyzing I/O Element Trace "
		<< anElement << "with AvmOpCode : "
		<< TracePoint::to_string(theAC.getAvmOpCode()) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( HIGH , PRE_FILTERING )

		switch( theAC.getAvmOpCode() )
		{
			//case AVM_OPCODE_ASSIGN_NEWFRESH :
			case AVM_OPCODE_INPUT:
			case AVM_OPCODE_OUTPUT:
			{
				// hardwired comparison
				if( theAC.first().is< InstanceOfPort >() )
				{
					const InstanceOfPort & aPort =
							theAC.first().to< InstanceOfPort >();
					const InstanceOfPort & ioPort = ( aPort.hasAliasTarget()
							? aPort.getAliasTarget()->as< InstanceOfPort >()
							: aPort );

					if( portInObsSignals(anExexConf.getRuntimeID(), ioPort,
							theAC.getAvmOpCode(), theAC.getOptimizedOpCode()) )
					{
						return true;
					}
				}
				break;
			}
			default:
			{
				for( const auto & itOperand : theAC.getOperands() )
				{
					if( hasObservableSignal(itOperand, anExexConf) )
					{
						return true;
					}
				}

				return false;
			}
		}

		return false;
	}

	return false;
}

bool OfflineTestProcessor::prefilter(ExecutionContext & anEC)
{
	OfflineTestProcessorInfo * currentOfflineTestInfo =
			anEC.getUniqInformation()
			->getUniqSpecificInfo< OfflineTestProcessorInfo >();

	if( anEC.hasPrevious() )
	{
		OfflineTestProcessorInfo * previousOfflineTestInfo = nullptr;

		TraceSequence theLocalTrace;

		// Get "trace" (vector of pair of variable value), which is
		// the one of its parent (previous)
		if( anEC.getPrevious()->hasInformation() )
		{
			previousOfflineTestInfo = anEC.getPrevious()->getInformation()
					->getUniqSpecificInfo< OfflineTestProcessorInfo >();

			theLocalTrace = previousOfflineTestInfo->getLocalTrace();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Its previous EC: " << anEC.getPrevious()->str_min()
			<< " IO Trace: " << anEC.getPrevious()->getIOElementTrace();
	printTrace( previousOfflineTestInfo->getLastObs() , "The (Last Obs) trace:", "\t" );
	AVM_OS_LOG << "Its previous trace size is: "
			<< previousOfflineTestInfo->getLocalTrace().points.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		}
		else
		{
			previousOfflineTestInfo = anEC.getPrevious()->getUniqInformation()
					->getUniqSpecificInfo< OfflineTestProcessorInfo >();
		}


		if( previousOfflineTestInfo->isAnalyzedMark() )
		{

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Verdict already computed!!!!!!!!!! for EC: "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

			return false;

		}

		bool hasNoneObsInEC = (not hasObservableSignal(anEC.getIOElementTrace()));

		if( hasNoneObsInEC )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "jumping!!!!!!!! not interesting!!!!!!!! for EC: "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		}

		if(timedFlag)
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "setting reference of father in EC: "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

			currentOfflineTestInfo->setTimeReference(
					previousOfflineTestInfo->getTimeReference());

			currentOfflineTestInfo->setTimeElapsing(
					previousOfflineTestInfo->getTimeElapsing() );
		}

		if( theTrace.points.empty()
			|| hasNoneObsInEC
			|| previousOfflineTestInfo->isAnalyzedMark()
			|| (not hasIOTrace(anEC.getIOElementTrace())) )
		{

			currentOfflineTestInfo->setLocalTrace(
					previousOfflineTestInfo->getLocalTrace());

			currentOfflineTestInfo->setLastObs(
					previousOfflineTestInfo->getLastObs());

			currentOfflineTestInfo->setLastTransition(
					previousOfflineTestInfo->getLastTransition());

			currentOfflineTestInfo->setAnalyzedMark(
					previousOfflineTestInfo->isAnalyzedMark() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Trace already read, or tau, or already failed/inconci, "
			"or projecting,\nassigning and skipping EC: " << anEC.str_min()
			<< std::endl
			<< "Local Trace size : "
			<< currentOfflineTestInfo->getLocalTrace().points.size()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

			return true;
		}

		// the last observation is stored in the node (to find a match in the trace)
		TraceSequence lastObs;
		makeLocalObs(lastObs, theLocalTrace, this->timedFlag);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "The local trace is (assigned!): " << std::endl;
	printTrace(theLocalTrace);
	AVM_OS_COUT << "\nOfflineTestProcessor::prefilter(...) EC:> "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )


		if( AssignValuesIfObservable(anEC, theLocalTrace) )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		AVM_OS_LOG << "Something was read " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

			// assign last obs (since something was read/localObs was modified)
			currentOfflineTestInfo->setLastObs(lastObs);
			currentOfflineTestInfo->setLastTransition(
					anEC.getRunnableElementTrace());
			// each EC has its own copy of the trace
			currentOfflineTestInfo->setLocalTrace(theLocalTrace);

			// checking trace length
			if( currentOfflineTestInfo->getLocalTrace().points.empty() )
			{
				// the trace is finished for this path, set the flag to true so we don't
				// continue calculating
				currentOfflineTestInfo->setAnalyzedMark(true);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "The flag was set to true, this tree path should stop at EC: "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
			}
		}
		else
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Nothing was read in this EC: " << anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

			// it was necessarily an input or an output that was not read, so we mark
			// the entire path so we don't analyze it anymore (the verdict will be
			// emitted later
			currentOfflineTestInfo->setAnalyzedMark(true);

			// assign last obs of parent (since nothing was read)
			currentOfflineTestInfo->setLastObs(
					previousOfflineTestInfo->getLastObs());

			currentOfflineTestInfo->setLastTransition(
					previousOfflineTestInfo->getLastTransition());

			// each EC has its own copy of the trace
			currentOfflineTestInfo->setLocalTrace(
					previousOfflineTestInfo->getLocalTrace());
		}
	}

	else if( anEC.getHeight() <= 0 )
	{
		currentOfflineTestInfo->setLocalTrace(theTrace);
		makeLocalObs(currentOfflineTestInfo->getLastObs(), theTrace, this->timedFlag);

		// Setting time reference when system is timed
		if(timedFlag)
		{
			const BF & referenceTimeVar = ENV.getRvalue(anEC.getwExecutionData(),
				anEC.getExecutionData().getSystemRID(), (* timeReferenceInstance));

			currentOfflineTestInfo->setTimeReference(referenceTimeVar);

			currentOfflineTestInfo->setTimeElapsing(referenceTimeVar);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "1. Setting time reference to " << referenceTimeVar.str()
		<< std::endl
		<< "The Time Reference Instance is: "
		<< timeReferenceInstance->getQualifiedNameID()
		<< std::endl
		<< currentOfflineTestInfo->getTimeReference().str()
		<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		}


		if( anEC.hasRunnableElementTrace() )
		{
			currentOfflineTestInfo->setLastTransition(
					anEC.getRunnableElementTrace());

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Root does have Runnable Element Trace! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		}
		else
		{
			currentOfflineTestInfo->setLastTransition(BF::REF_NULL);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Root does NOT have Runnable Element Trace! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
		}
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Root, assigning and skipping: " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )

		return true;
	}

	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	AVM_OS_LOG << "Warning in PROCESSOR Prefilter: node without previous? "
			"Is it the Root ?" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PRE_FILTERING )
	}

	return true;
}

////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool OfflineTestProcessor::postfilter()
{
	ecQueue = &( getExecutionQueue().getResultQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; )
	{
		if( not postfilter(* (*ecQueueIt)) )
		{
			AVM_OS_LOG << "FAIL in postfilter offline test!" << std::endl;

			return false;
		}
		else
		{
			++ecQueueIt;
		}
	}

	return (getExecutionQueue().hasResult());
}

bool OfflineTestProcessor::postfilter(ExecutionContext & anEC)
{
	if( (anEC.getHeight() <= 0)
		|| (theTrace.points.size() == 0)
		|| (not hasIOTrace(anEC.getIOElementTrace()))
		|| (not hasObservableSignal(anEC.getIOElementTrace())) )
	{
		return true;
	}

	OfflineTestProcessorInfo * currentOfflineTestInfo =
			anEC.getUniqInformation()
			->getUniqSpecificInfo< OfflineTestProcessorInfo >();


	// set THIS current time (since it is not a tau, nor it was projected)
	// in case when the system is timed
	if(timedFlag)
	{
		const BF & referenceTimeVar = ENV.getRvalue(anEC.getwExecutionData(),
			anEC.getExecutionData().getSystemRID(), (* timeReferenceInstance));

		currentOfflineTestInfo->setTimeReference(referenceTimeVar);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "2. Setting time reference to "
			<< referenceTimeVar.str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}


//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << "The level nodes is now: " << std::endl;
//	ListOfExecutionContext::iterator itl = theLevelNodes.begin();
//	ListOfExecutionContext::iterator endItl = theLevelNodes.end();
//	for( ; itl != endItl ; itl++)
//	{
//		AVM_OS_LOG << "EC: " << (*itl)->str_min() << std::endl;
//	}
//	AVM_OS_LOG << "CUrr height: " << anEC.getHeight() << std::endl;
//			<< "waiting top EC: " << getExecutionQueue().topWaiting()->str_min()
//			<< std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	/*
	// only if the next context to execute is in a new level of the tree, we
	// examine what happened with all the nodes in the same level
	if( not getExecutionQueue().hasWaiting() ||
		getExecutionQueue().topWaiting()->getHeight() !=  anEC.getHeight() )
	{
//we are in a new level:
//	1. update height
//	2. remove first obs from trace, keep it in lastObs
//	3. according to the set of localObs of all execution contexts of the
//	previous height, give verdicts:
//		3.1 if there is at least one empty obs, it is because it was
//		read/accepted by a node in the tree
//			3.1.1 if the node for which the obs is empty is in the path,
//				if the trace is empty, incr PASS
//			3.1.2 if the node for which the obs is empty is not in the path,
//				if the trace is empty, incr WeakPASS
//			3.2 if the trace is empty:
//			3.2.1 if PASS > 0 and WeakPASS > 0, emit WeakPASS
//			3.2.2 if PASS > 0 and WeakPASS == 0, emit PASS
//			3.2.3 if PASS == 0 and WeakPASS > 0, emit INCONCr
//		3.3 if there is no empty obs, it is because no node read/accepted the trace:
//			3.3.1 if lastObs is an input, emit INCONC?
//			3.3.2 if lastObs is an output or a delay, emit FAIL
//		3.4 if there is an obs and the trace is not empty, continue
//	4. clear the level nodes


		// step 1
		theHeight = anEC.getHeight();

		// step 2
		TraceOfObs lastObs;
		makeLocalObs(lastObs, theTrace);
		removeOneObs(theTrace);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "ahora el size de la trace es " << theTrace.size() <<std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		// step 3
		// parcour all nodes in the list
		ListOfExecutionContext::iterator itl = theLevelNodes.begin();
		ListOfExecutionContext::iterator endItl = theLevelNodes.end();
		int emptyObs = 0;
		int weakPASS = 0;
		int PASS = 0;
		for( ; itl != endItl ; itl++)
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "verdict analizing EC: " << (*itl)->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			bool flag = false;
			transitionInTestPurpose(
					(*itl)->getRunnableElementTrace(), theTestPurpose, flag);

			const TraceOfObs & aLocalObs = (*itl)->getUniqInformation()
					->getUniqSpecificInfo< OfflineTestProcessorInfo >()
					->getLocalObs();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "size of local obs is : " << aLocalObs.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			if( aLocalObs.empty() )
			{
				// it means this node accepted the head of the trace
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Size 0 for EC: " << (*itl)->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				emptyObs++;

				if( theTrace.size() == 0 )
				{
					// weakPASS or PAS
					flag=false;
					transitionInTestPurpose(
						(*itl)->getRunnableElementTrace(), theTestPurpose, flag);
					if( flag )
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Found in test purpose, pass!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

						PASS ++;
					}
					else
					{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Not found in test pourpose, weakPass" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

						weakPASS ++;
					}

				}
			}
		}

		// we delete the first transition in the list, since we changed of
		// level in the tree
		if( not theTestPurpose.empty() )
		{
			theTestPurpose.erase(theTestPurpose.begin());

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "NOW The test purpose (sequence of transition names) is: "
			<< std::endl;
	for( VectorOfString::iterator i = theTestPurpose.begin() ;
			i != theTestPurpose.end() ; ++i )
	{
		AVM_OS_LOG << *i << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
		else
		{
			AVM_OS_WARN << "Error: Test purpose is empty before expected! "
					<< std::endl;
			return false;
		}

		// step 3.2
		if( theTrace.size() ==0 && emptyObs > 0 )
		{
			if( weakPASS > 0 )
			{
				if( PASS == 0 )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is InconcR!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "INTONCr";
					theVerdictKind = VERDICT_INCONCr_KIND;
				}
				else
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Weak Pass!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "weakPASS";
					theVerdictKind = VERDICT_WEAK_PASS_KIND;
				}
			}
			else if( PASS > 0 )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Pass!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				verdictEmitted = true;
				theVerdict = "PASS";
				theVerdictKind = VERDICT_PASS_KIND;
			}


		}

		// step 3.3
		// if there is no empty obs, it is because no node read/accepted
		// the trace:
		// 3.2.1 if lastObs is an input, emit INCONC?
		// 3.2.2 if lastObs is an output or a delay, emit FAIL
		if( emptyObs == 0 )
		{
			if( lastObs.first().first().is< InstanceOfData >() &&
				(theTimeVarInstance->getNameID() ==
					lastObs.first().first().to< InstanceOfData >().getNameID()) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Sense of observation is: "
			<< lastObs.second().second().str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				if( lastObs.second().second().str() == "?" )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Inconc?" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "INCONC?";
					theVerdictKind = VERDICT_INCONCi_KIND;
				}
				else {
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Fail!" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "FAIL";
					theVerdictKind = VERDICT_FAIL_KIND;
				}
			}
			else
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Sense of observation is: "
			<< lastObs.first().second().str() <<std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				if( lastObs.first().second().str() == "?" )
				{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Inconc? " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "INCONC?";
					theVerdictKind = VERDICT_INCONCi_KIND;
				}
				else {
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Fail! " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

					verdictEmitted = true;
					theVerdict = "FAIL";
					theVerdictKind = VERDICT_FAIL_KIND;
				}
			}

		}

		// step 3.4
		if( theTrace.size() > 0 && emptyObs > 0 )
		{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Continue reading " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}

		for( const auto & itChildEC : anEC->getChildContexts() )
		{
			// noop??
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Nested noop " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}

		theLevelNodes.clear();
	}
	else
	{www.npr.org/blogs/ed/2014/08/22/341898975/a-picture-of-language-the-fading-art-of-diagramming-sentences
		// we are in the same level
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Not analyzing, out " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}
*/
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "==> Rule: continue " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	return( true );
}

////////////////////////////////////////////////////////////////////////////////
// POST-PROCESS API
////////////////////////////////////////////////////////////////////////////////

void OfflineTestProcessor::searchLeaves(const ExecutionContext & anEC)
{
	if( anEC.isLeafNode() && anEC.isnotRoot() )
	{
		// it is a leaf, take its parent
		// (the last leave is not evaluated by the filters)
		if( not theLeavesECVector.contains(anEC.getPrevious()) )
		{
			theLeavesECVector.append( anEC.getPrevious() );

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "LEAF!!! local Trace size : "
			<< anEC.getPrevious()->getUniqInformation()
			->getUniqSpecificInfo< OfflineTestProcessorInfo >()
			->getLocalTrace().points.size()
			<< " => the EC: " << anEC.getPrevious()->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
	}
	else
	{
		// recursive lookup
		for( const auto & itChildEC : anEC.getChildContexts() )
		{
			searchLeaves( *itChildEC );
		}
	}
}

bool OfflineTestProcessor::postprocess()
{
	AVM_OS_LOG << "OfflineTestProcessor::postprocess()" << std::endl;

	theLeavesECVector.clear();
	searchLeaves( getConfiguration().getFirstExecutionTrace() );
	if( theLeavesECVector.empty() )
	{
		AVM_OS_LOG << "ZERO LEAVE :> FAILED !" << std::endl;
		theVerdict = "FAILED";
		theVerdictKind = VERDICT_FAIL_KIND;

		return( true );
	}

	// list of execution contexts that will store the ones with the smallest traces
	List< ExecutionContext * >  smallestTraces(theLeavesECVector.pop_first());

	theSmallestTraceEC = theLeavesECVector.first();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "1. Smallest traces size :" << smallestTraces.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	OfflineTestProcessorInfo * offlineTestInfo = nullptr;

	// check the local trace, last obs and last transition for every leaf
	for( const auto & leafEC : theLeavesECVector )
	{
		offlineTestInfo = leafEC->getInformation()
				->getUniqSpecificInfo< OfflineTestProcessorInfo >();

		//theInformationVector.clear();
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "For this leave EC: " << leafEC->str_min() << std::endl
			<< "\tlast obs: " << std::endl;
	//printTrace(offlineTestInfo->getLastObs());
	if( offlineTestInfo->getLastTransition().valid() )
	{
		AVM_OS_LOG << "Last trans :" << std::endl
				<< offlineTestInfo->getLastTransition().str()
				<< std::endl;
		AVM_OS_LOG << "Local trace size :" << std::endl
				<< offlineTestInfo->getLocalTrace().points.size()
				<< std::endl;
		AVM_OS_LOG << "Local trace :" << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		if( offlineTestInfo->getLastTransition().valid() &&
			(offlineTestInfo->getLocalTrace().points.size() <
				smallestTraces.first()->getInformation()
					->getUniqSpecificInfo< OfflineTestProcessorInfo >()
					->getLocalTrace().points.size()) )
		{
			// we found a smaller trace: clear the list and initialize it with this EC
			smallestTraces.clear();
			smallestTraces.append(leafEC);

			theSmallestTraceEC = leafEC;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Is smallest!" << std::endl;
	AVM_OS_LOG << offlineTestInfo->isAnalyzedMark() << std::endl;
	if( offlineTestInfo->isAnalyzedMark() )
	{
		AVM_OS_LOG << "Is marked!" << std::endl;
	}
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
		else if( (offlineTestInfo->getLocalTrace().points.size() ==
					smallestTraces.first()->getInformation()
						->getUniqSpecificInfo< OfflineTestProcessorInfo >()
						->getLocalTrace().points.size())
				&& offlineTestInfo->getLastTransition().valid() )
		{
			// we found another node/path accepting the trace
			//  we need to check if the transition is different that all the elements in the list...
//			bool flag = false;
//			// TODO: intelligent way to check for repeated transitions? is that possible?
////			transitionInList(leafEC->getInformation()->
////					getUniqOfflineTestProcessorInfo()->getLastTransition(),
////					repeatedTraces, flag);
//			if( flag == false )
			{
				// different path accepting the same trace
				smallestTraces.append(leafEC);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Is repeated!!!!" << std::endl
			<< "And LastTransition: " << offlineTestInfo->getLastTransition().str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}
		}
	}

	// now, smallestTraces is the list of smallest traces, let's emit a verdict

	int PASS = 0, weakPASS = 0, INCONCi = 0, FAIL = 0;

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "2. Smallest traces size :" << smallestTraces.size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )


	// we go through the entire list...
	for( const auto & itEC : smallestTraces )
	{
		offlineTestInfo = itEC->getInformation()
				->getUniqSpecificInfo< OfflineTestProcessorInfo >();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Smallest trace :" << std::endl;
	printTrace(offlineTestInfo->getLocalTrace());
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		if( offlineTestInfo->getLocalTrace().points.size() == 0 )
		{
			bool flag = false;
			// if no test purpose was specified, then PASS
			if(theTestPurpose.points.empty())
			{
				AVM_OS_LOG << "NB: The verdict was computed with no test purpose. " << std::endl;
				flag = true;
			}
			// else, is the last transition part of the test purpose ?
			else
			{
				flag = testPurposeContainsElement(theTestPurpose,
						itEC->getInformation()->getUniqSpecificInfo
							< OfflineTestProcessorInfo >()->getLastTransition());
			}
			//is itEC a PASS, weakPASS or a INCONCr?
			if( flag )
			{
				itEC->getwFlags().setObjectiveAchievedTrace();

				itEC->addInfo(*this, INFO_OFFLINETEST_DATA_PASS);
				PASS++;

				thePassEC.append(itEC);
			}
			else
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Size is 0, but transition not in TP of the EC: "
			<< itEC->str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				weakPASS++;
			}
		}
		else
		{
			// retrieve the tracePoint of the first action in localTrace
			// if aTracePoint is a controllable input, emit INCONC?
			// if aTracePoint is an output or an uncontrollable input, emit FAIL

			TracePoint * aTracePoint = offlineTestInfo->
					getLocalTrace().points.first().to_ptr<TracePoint>();

			if( aTracePoint->isTime()
				&& offlineTestInfo->getLocalTrace().points.populated()
				&& ( (theTimeVarInstance == aTracePoint->object)
					/*|| (theTimeVarInstance->getNameID()
							== aTracePoint->object->getNameID())*/ ) )
			{
				aTracePoint = offlineTestInfo->
						getLocalTrace().points.second().to_ptr<TracePoint>();
			}
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "(1) Direction of observation is: "
			<< 	aTracePoint->to_string(aTracePoint->op) << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

			if( (aTracePoint->op == AVM_OPCODE_INPUT_ENV) &&
				portInCtrlSignals(*aTracePoint) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Inconc? for the EC: " << itEC->str_min()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				INCONCi++;
				break;
			}
			else if( (aTracePoint->op == AVM_OPCODE_INPUT) &&
				portInCtrlSignals(*aTracePoint) )
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Inconc? for the EC: " << itEC->str_min()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				INCONCi++;
				break;
			}
			else
			{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Verdict is Fail! (output of the form d.a"
			" --with a output or delay)" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

				FAIL++;
				break;
			}

		}

	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Counters: "
			<< "PASS: " << PASS << std::endl
			<< "WeakPASS: " << weakPASS << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	// let's emit the verdict
	if( PASS > 0 && weakPASS == 0 )
	{
		if( PASS > 1 && theTestPurpose.points.empty() )
		{
			theVerdictKind = VERDICT_WEAK_PASS_KIND;

			theVerdict = " THE VERDICT IS : WEAK PASS< non-determinism >";
		}
		else
		{
			theVerdictKind = VERDICT_PASS_KIND;

			theVerdict = " THE VERDICT IS : PASS ";
		}

		verdictEmitted = true;
	}
	else if( PASS > 0 && weakPASS > 0 )
	{
		theVerdictKind = VERDICT_WEAK_PASS_KIND;

		theVerdict = " THE VERDICT IS : weakPASS ";
		verdictEmitted = true;
	}
	else if( PASS == 0 && weakPASS > 0 )
	{
		theVerdictKind = VERDICT_INCONCr_KIND;

		theVerdict = " THE VERDICT IS : INCONCr ";
		verdictEmitted = true;
	}
	else if( INCONCi > 0 )
	{
		theVerdictKind = VERDICT_INCONCi_KIND;

		theVerdict = " THE VERDICT IS : INCONCi ";
		verdictEmitted = true;
	}
	else if( FAIL > 0 )
	{
		theVerdictKind = VERDICT_FAIL_KIND;

		theVerdict = " THE VERDICT IS : FAIL ";
		verdictEmitted = true;
	}

	else
	{
		theVerdictKind = VERDICT_ABORT_KIND;
	}

	if( verdictEmitted == true )
	{
//AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
//	AVM_OS_LOG << EMPHASIS(theVerdict, '=', 80);
//AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}
	else
	{
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_WARN << "ERROR ! something went wrong, no verdict emitted! "
				<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	}

	// FINAL SLICING
	finalSlicing();

	return true;
}


////////////////////////////////////////////////////////////////////////////
// FINAL SLICING TOOLS
////////////////////////////////////////////////////////////////////////////

bool OfflineTestProcessor::isSliceableContext(ExecutionContext & anEC) const
{
	if( (theVerdictKind == VERDICT_PASS_KIND)
		|| (theVerdictKind == VERDICT_WEAK_PASS_KIND) )
	{
		return( anEC.getFlags().noneObjectiveAchievedTrace() );
	}
	else
	{
//		return( anEC.getFlags().noneCoverageElementTrace() );
		return false;
	}
}

bool OfflineTestProcessor::finalSlicing()
{
	if( mSliceFlag )
	{
		ListOfExecutionContext listOfLeafEC;

		// ELAGAGE DANS TOUT LE GRAPH!!!!!
		computeLeafEC(getConfiguration().getExecutionTrace(), listOfLeafEC);

		slice(listOfLeafEC);
	}

	return( true );
}




/**
 * EXIT API
 */
bool OfflineTestProcessor::exitImpl()
{
	// SET EXIT CODE
	switch( theVerdictKind )
	{
		case VERDICT_PASS_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_PASS_CODE );
			break;
		}
		case VERDICT_WEAK_PASS_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_WEAK_PASS_CODE );
			break;
		}
		case VERDICT_INCONCr_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_INCONCLUSIVE_REACTION_CODE);
			break;
		}
		case VERDICT_INCONCi_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_INCONCLUSIVE_INPUT_CODE );
			break;
		}
		case VERDICT_FAIL_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_FAIL_CODE );
			break;
		}
		case VERDICT_ABORT_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_ABORT_CODE );
			break;
		}
		case VERDICT_UNDEFINED_KIND:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_UNDEFINED_CODE );
			break;
		}
		default:
		{
			avm_set_exit_code( AVM_EXIT_VERDICT_ABORT_CODE );
			break;
		}
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void OfflineTestProcessor::tddRegressionReportImpl(OutStream & os) const
{
	os << TAB << "THE VERDICT IS : ";

	switch( theVerdictKind )
	{
		case VERDICT_PASS_KIND:
		{
			os << "PASS";
			break;
		}
		case VERDICT_WEAK_PASS_KIND:
		{
			os << "WEAK_PASS";
			break;
		}
		case VERDICT_INCONCr_KIND:
		{
			os << "INCONCr";
			break;
		}
		case VERDICT_INCONCi_KIND:
		{
			os << "INCONCi";
			break;
		}
		case VERDICT_FAIL_KIND:
		{
			os << "FAIL";
			break;
		}
		case VERDICT_ABORT_KIND:
		{
			os << "ABORT";
			break;
		}
		case VERDICT_UNDEFINED_KIND:
		{
			os << "UNDEFINED";
			break;
		}
		default:
		{
			os << "ABORT";
			break;
		}
	}

	os << EOL_FLUSH;
}

/**
 * Info Serialization
 */
void OfflineTestProcessorInfo::toStream(OutStream & os)  const
{
	if( theLastObs.points.nonempty() )
	{
		os << TAB << "TABLE{" << EOL;

		os << TAB << "}" << EOL_FLUSH;
	}
}

void OfflineTestProcessorInfo::toFscn(OutStream & os) const
{
	if( theLastObs.points.nonempty() )
	{
		os << TAB << "TABLE{" << EOL;
		os << TAB << "}" << EOL_FLUSH;
	}
}


} /* namespace sep */
