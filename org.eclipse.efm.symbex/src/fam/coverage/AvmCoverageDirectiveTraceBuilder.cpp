/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 17 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmCoverageDirectiveTraceBuilder.h"

#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/AvmTransition.h>

#include <fml/expression/StatementTypeChecker.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fam/coverage/AvmCoverageTransitionView.h>
#include <fml/runtime/Message.h>


namespace sep
{


/**
 * Utils for TraceSequence
 */
void AvmTraceProperty::checkDecrementation(AvmTransition * aTransition)
{
	if( (mTransitionCoverage != NULL) &&
		(not mTransitionCoverage->testTransitionCoverage(aTransition)) )
	{
		--mUncoveredCount;
	}

	if( aTransition->hasStatementGuardFamily() )
	{
		--mGuardCount;
	}
	else if( aTransition->isUnconditionalStatementFamily() )
	{
		--mUnconditionalCount;
	}

	if( aTransition->isUnstableSource() )
	{
		--mUnstableCount;
	}
}

void AvmTraceProperty::checkIncrementation(AvmTransition * aTransition)
{
	if( (mTransitionCoverage != NULL) &&
		(not mTransitionCoverage->testTransitionCoverage(aTransition)) )
	{
		++mUncoveredCount;
	}

	if( aTransition->hasStatementGuardFamily() )
	{
		++mGuardCount;
	}
	else if( aTransition->isUnconditionalStatementFamily() )
	{
		++mUnconditionalCount;
	}

	if( aTransition->isUnstableSource() )
	{
		++mUnstableCount;
	}
}


void AvmTraceProperty::updadeSize()
{
	mSize = 0;
	mUncoveredCount = 0;
	mGuardCount = 0;
	mUnconditionalCount = 0;
	mUnstableCount = 0;

	BFList::const_iterator itPoint = points.begin();
	BFList::const_iterator endPoint = points.end();
	for( ; itPoint != endPoint ; ++itPoint )
	{
		++mSize;

		checkIncrementation( (*itPoint).to_ptr< TracePoint >()->
				object->as< AvmTransition >() );
	}
}


bool AvmTraceProperty::compare( bool (* isComp)(avm_size_t, avm_size_t),
		const AvmTraceProperty & aTraceElement )
{
	return( isComp(xSize(), aTraceElement.xSize()) );
}


/**
 * Serialization
 */
void AvmTraceProperty::toStream(OutStream & os, bool verbose) const
{
	os << TAB << "trace#" << tid
			<< "<xsize:" << xSize() << ", size:" << mSize
			<< ", uncovered:" << mUncoveredCount
			<< ", guard:" << mGuardCount
			<< ", uncondional:" << mUnconditionalCount
			<< ", unstable:" << mUnstableCount << ">";
	if( mEC != NULL )
	{
		if( verbose )
		{
			os << EOL_TAB << AVM_STR_INDENT;
			mEC->traceMinimum(os);
			os << END_INDENT;
		}
		else
		{
			os << "( ctx:" << mEC->getIdNumber() << " )";
		}
	}
	if( points.nonempty() )
	{
		os << " --> " << backTransition()->getNameID();
	}
	os << " { " << combinator->strOp() << EOL;

	if( verbose  )
	{
		os << INCR_INDENT;
		BFList::const_iterator itPoint = points.begin();
		BFList::const_iterator endPoint = points.end();
		for( AvmTransition * aTransition = NULL ; itPoint != endPoint ; ++itPoint )
		{
			aTransition = (*itPoint).to_ptr< TracePoint >()->
					object->as< AvmTransition >();

			(*itPoint).toStream(os);

			os << TAB2 << "\t\t\t--> " << aTransition->strTargetId();
			os << " \t==> " << aTransition->strStatementFamily() << EOL;
			if ( aTransition->hasInternalCommunicationCode() )
			{
				os << TAB2 << "\t\t\t";
				BaseCompiledForm::toStreamStaticCom(os,
						aTransition->getInternalCommunicationCode() );
			}
		}
		os << DECR_INDENT;
	}
	else
	{
		os << INCR_INDENT << points << DECR_INDENT;
	}

	os << TAB << "}" << EOL_FLUSH;
}


/**
 * CONSTRUCTOR
 * Default
 */
AvmCoverageDirectiveTraceBuilder::AvmCoverageDirectiveTraceBuilder(
		const ExecutionContext * anEC, TracePoint * tpTransition,
		ENUM_HEURISTIC_CLASS anHeuristicClass,
		avm_size_t pathCountLimit, avm_size_t pathSizeLimit)
: IHeuristicClass( anHeuristicClass ),

mEC( anEC ),
mED( anEC->getAPExecutionData() ),
mRID( tpTransition->RID ),

mTransition( tpTransition->object->to< AvmTransition >() ),
mTransitionPoint( tpTransition ),

mTraceElement( ),

mComputingPathCountLimit( pathCountLimit ),
mComputingPathSizeLimit( pathSizeLimit ),

mGoalAchievedFlag( false ),

//mTransitionPath( ),
//mExpectedInput( ),
mVirtualBuffer(mTransition, NULL, 0, TYPE_MULTI_LIFO_SPECIFIER, -1),
mEmitOutput( & mVirtualBuffer ),

mTableOfRuntimeStatus( *( mED->getRuntimeFormStateTable() ) ),

// computing variable for method << computePathToTransition >>
anyTransitionPaths( ),
prefixLoopTransitionPaths( ),

outgoingTransitions( ),
aTransitionPath( ),
itTrans( ),
endTrans( ),

tgtInstance( NULL ),
fwdMachine( NULL ),
tgtMachine( NULL )
{
	//!! NOTHING
}

AvmCoverageDirectiveTraceBuilder::AvmCoverageDirectiveTraceBuilder(
		const ExecutionContext * anEC, const RuntimeID & aRID,
		AvmTransition * aTransition, ENUM_HEURISTIC_CLASS anHeuristicClass,
		avm_size_t pathCountLimit, avm_size_t pathSizeLimit)
: IHeuristicClass( anHeuristicClass ),

mEC( anEC ),
mED( anEC->getAPExecutionData() ),
mRID( aRID ),

mTransition( aTransition ),
mTransitionPoint( NULL ),

mTraceElement( ),

mComputingPathCountLimit( pathCountLimit ),
mComputingPathSizeLimit( pathSizeLimit ),

mGoalAchievedFlag( false ),

//mTransitionPath( ),
//mExpectedInput( ),
mVirtualBuffer(mTransition, NULL, 0, TYPE_MULTI_LIFO_SPECIFIER, -1),
mEmitOutput( & mVirtualBuffer ),

mTableOfRuntimeStatus( *( mED->getRuntimeFormStateTable() ) ),

// computing variable for method << computePathToTransition >>
anyTransitionPaths( ),
prefixLoopTransitionPaths( ),

outgoingTransitions( ),
aTransitionPath( ),
itTrans( ),
endTrans( ),

tgtInstance( NULL ),
fwdMachine( NULL ),
tgtMachine( NULL )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// Configure
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageDirectiveTraceBuilder::configure(
		AvmTraceProperty & aTraceElement, const ExecutionContext * anEC,
		TracePoint * tpTransition, ENUM_HEURISTIC_CLASS anHeuristicClass,
		avm_size_t pathCountLimit, avm_size_t pathSizeLimit)
{
	mEC =  anEC,
	mED = anEC->getAPExecutionData();

	mRID = tpTransition->RID;
	mTransition = tpTransition->object->to< AvmTransition >();

	mTransitionPoint = tpTransition;

	mTraceElement.configure( aTraceElement );

	mHeuristicClass = anHeuristicClass;

	mComputingPathCountLimit = pathCountLimit;
	mComputingPathSizeLimit  = pathSizeLimit;

	mTableOfRuntimeStatus.reset(
			*( mED->getRuntimeFormStateTable() ), false);

	return( true );
}

bool AvmCoverageDirectiveTraceBuilder::configure(
		AvmTraceProperty & aTraceElement, const ExecutionContext * anEC,
		const RuntimeID & aRID, AvmTransition * aTransition,
		ENUM_HEURISTIC_CLASS anHeuristicClass,
		avm_size_t pathCountLimit, avm_size_t pathSizeLimit)
{
	mEC =  anEC,
	mED = anEC->getAPExecutionData();

	mRID = aRID;
	mTransition = aTransition;

	mTransitionPoint = NULL;

	mTraceElement.configure( aTraceElement );

	mHeuristicClass = anHeuristicClass;

	mComputingPathCountLimit = pathCountLimit;
	mComputingPathSizeLimit  = pathSizeLimit;

	mTableOfRuntimeStatus.reset( *( mED->getRuntimeFormStateTable() ), false);

	return( true );
}



////////////////////////////////////////////////////////////////////////////////
// API
////////////////////////////////////////////////////////////////////////////////

bool AvmCoverageDirectiveTraceBuilder::initialize()
{
	mGoalAchievedFlag = false;

	mEmitOutput.clear();

	if( mRID.invalid() )
	{
		if( mED->mRID.getExecutable()->getTransition().contains(mTransition) )
		{
			mRID = mED->mRID;
		}

		if( mRID.invalid() )
		{
			if( mTransitionPoint != NULL )
			{
				mTransitionPoint->updateRID( (* mED) );

				mRID = mTransitionPoint->RID;
			}
			else
			{
				mRID = mED->getRuntimeID( mTransition->getExecutable() );
			}
		}
	}

	return( mRID.valid() );
}


bool AvmCoverageDirectiveTraceBuilder::computePath()
{
	if( initialize() )
	{
		AvmCommunicationFactory::collectBufferMessage(mED, mEmitOutput);

		return( mGoalAchievedFlag = computePath(mRID, mTransition) );
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computePath(
		AvmTraceProperty & aTraceElement)
{
	if( initialize() )
	{
		AvmCommunicationFactory::collectBufferMessage(mED, mEmitOutput);

		if( computePath(mRID, mTransition) )
		{
			aTraceElement.copyTrace( mTraceElement );

			mGoalAchievedFlag = true;

			return( true );
		}
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computePath(
		AvmTraceProperty & aTraceElement, ExecutionContext * anEC,
		const RuntimeID & aRID, AvmTransition * aTransition,
		ENUM_HEURISTIC_CLASS anHeuristicClass,
		avm_size_t pathCountLimit, avm_size_t pathSizeLimit)
{
	if( configure(aTraceElement, anEC, aRID, aTransition,
			anHeuristicClass, pathCountLimit, pathSizeLimit) )
	{
		if( initialize() )
		{
			AvmCommunicationFactory::collectBufferMessage(mED, mEmitOutput);

			if( computePath(mRID, mTransition) )
			{
				aTraceElement.copyTrace( mTraceElement );

				mGoalAchievedFlag = true;

				return( true );
			}
		}
	}

	return( false );
}



void AvmCoverageDirectiveTraceBuilder::report(OutStream & os)
{
	os << DEFAULT_WRAP_DATA;

	if( mEC != NULL )
	{
		os << "from ";  mEC->traceMinimum(os);
	}
	os << "Trace to reach (size:" << mTraceElement.mSize << ") :> "
			<< mTransition->strTransitionHeader() << std::endl;
	mTraceElement.toStream(os);

//	os << "Expected Input :> " << std::endl;
//	BaseCompiledForm::toStreamStaticCom(os, mExpectedInput);
//	os << TAB << "Emit Output :>"; mEmitOutput.toStream(AVM_OS_TRACE);

	os << ( mGoalAchievedFlag ? "NEW" : "NO" ) << " OBJECTIVE !!!"
			<< END_WRAP << std::endl;
}



bool AvmCoverageDirectiveTraceBuilder::computePath(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "computePath from :> ";
	mEC->traceMinimum(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB2 << aRID.strUniqId() << " |==> ";
	aTransition->toStreamHeader(AVM_OS_TRACE); AVM_OS_TRACE << std::endl;
	if( aTransition->hasInternalCommunicationCode() )
	{
		AVM_OS_TRACE  << TAB2 << "com |==> ";
		BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE,
				aTransition->getInternalCommunicationCode());
	}
//	AVM_OS_TRACE << TAB << "Expected Input :> " << std::endl;
//	BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, mExpectedInput);
	AVM_OS_TRACE << TAB2 << "Emit Output :>"; mEmitOutput.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB << "end //computePath" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	if( mED->isIdleOrRunning(aRID) )
	{
		return( fireTransition(aRID, aTransition) );
	}
	else
	{
		return( computePathToTransition(aRID, aTransition) );
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::fireTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl
			<< TAB << "fireTransition :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
//	AVM_OS_TRACE << TAB2 << "Expected Input :> " << std::endl;
//	BaseCompiledForm::toStreamStaticCom(AVM_OS_TRACE, mExpectedInput);
	AVM_OS_TRACE << TAB2 << "Emit Output :>"; mEmitOutput.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB << "end //fireTransition" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	mTableOfRuntimeStatus.stateSet(aRID.getOffset(), PROCESS_SUSPENDED_STATE);

	if( aTransition->hasInputCom() )
	{
		ListOfInstanceOfPort anInputTrace( aTransition->getInputCom() );
		if( mEmitOutput.uncontains( anInputTrace /*, aRID*/ ) )
		{
			// trouver des émetteurs pour les INPUT attendu au regard de ED< SC >
			while( anInputTrace.nonempty() )
			{
				if( computePathToInput(aRID, anInputTrace.front()) )
				{
					anInputTrace.pop_front();
				}
				else
				{
					break;
				}
			}

			if( anInputTrace.empty() )
			{
				traceTransition(aRID, aTransition);

				return( true );
			}
			return( false );
		}
		else
		{
			traceTransition(aRID, aTransition);
		}
	}
	else
	{
		traceTransition(aRID, aTransition);
	}

	return( true );
}


void AvmCoverageDirectiveTraceBuilder::traceTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
	mTraceElement.append(aRID, aTransition);

	// Virtual Eval Of aTransition
	if( aTransition->hasOutputCom() )
	{
		ListOfInstanceOfPort::const_iterator itOutput =
				aTransition->getOutputCom().begin();
		ListOfInstanceOfPort::const_iterator endOutput =
				aTransition->getOutputCom().end();
		for( ; itOutput != endOutput ; ++itOutput )
		{
			mEmitOutput.push( Message(aRID, INCR_BF(*itOutput)) );
		}
	}
}


bool AvmCoverageDirectiveTraceBuilder::computePathToTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl
			<< TAB << "computePathToTransition using :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	RuntimeID tmpRID = aRID.getPRID();
	for( ; tmpRID.valid() ; tmpRID = tmpRID.getPRID() )
	{
		if( mED->isIdleOrRunning(tmpRID) )
		{
			break;
		}
	}

	AVM_OS_ASSERT_FATAL_ERROR_EXIT( tmpRID.valid() )
			<< "Unfound a Runnable Ancestor Statemachine !!!"
			<< SEND_EXIT;

	const RuntimeForm & tmpRF = mED->getRuntime(tmpRID);

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB2 << "Runnable Ancestor Statemachine :> "
			<< tmpRID.str() << std::endl
			<< TAB2 << "Runnable Ancestor State Scheduler :> {";
	tmpRF.getOnSchedule()->toStreamRoutine( AVM_OS_TRACE )
			<< TAB2 << "}" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	if( tmpRF.getOnSchedule()->isOpCode( AVM_OPCODE_RUN ) &&
		tmpRF.getOnSchedule()->first().is< RuntimeID >() )
	{
		return( computePathFromRunnable(
				tmpRF.getOnSchedule()->first().bfRID(), aTransition) );
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computeBasicPathFromRunnable(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl
			<< TAB << "computeBasicPathFromRunnable using :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	if( not aRID.getExecutable()->
			containsForwardReachableTransition(aTransition) )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		AVM_OS_TRACE << TAB2 << "Unreachable transition :> "
				<< mTransition->strTransitionHeader() << std::endl
				<< TAB2 << "from : " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

		return( false );
	}


AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "Looking for a path to :> " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	ListOfAvmTransition oneTransitionPath;

	if( computePathToTransition(aRID, aTransition, oneTransitionPath) )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << INCR_INDENT;
	AvmTransition::toStream(AVM_OS_TRACE, oneTransitionPath);
	AVM_OS_TRACE << DECR_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

		// All found path
//		ListOfListOfAvmTransition allTransitionPaths;
//		computePathToTransition(aRID, aTransition, allTransitionPaths);

		RuntimeID tmpRID = aRID;
		do
		{
			aTransition = oneTransitionPath.front();

			if( fireTransition(tmpRID, aTransition) )
			{
				oneTransitionPath.pop_front();

				computeTargetMachine(tmpRID, aTransition->getCode());
			}
			else
			{
				break;
			}
		}
		while( oneTransitionPath.nonempty() );

		return( oneTransitionPath.empty() );
	}

	return( false );
}



bool AvmCoverageDirectiveTraceBuilder::computeSmartPathFromRunnable(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << std::endl
			<< TAB << "computeSmartPathFromRunnable using :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	if( not aRID.getExecutable()->
			containsForwardReachableTransition(aTransition) )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
		AVM_OS_TRACE << TAB2 << "Unreachable transition :> "
				<< mTransition->strTransitionHeader() << std::endl
				<< TAB2 << "from : " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

		return( false );
	}


AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "Looking for a path to :> " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	avm_size_t saveTraceElementSize = mTraceElement.mSize;

	if( mComputingPathSizeLimit <= saveTraceElementSize )
	{
		return( false );
	}

	// All found path
	ListOfListOfAvmTransition allTransitionPaths;
	computePathToTransition(aRID, aTransition, allTransitionPaths);

	ListOfAvmTransition oneTransitionPath;
	RuntimeID tmpRID;

//	if( computePathToTransition(aRID, aTransition, oneTransitionPath) )
	while( allTransitionPaths.nonempty() )
	{
		oneTransitionPath.clear();
		oneTransitionPath.splice( allTransitionPaths.front() );
		allTransitionPaths.pop_front();

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "Found Path --> "
			<< aTransition->getFullyQualifiedNameID() << std::endl << INCR_INDENT;
	AvmTransition::toStream(AVM_OS_TRACE, oneTransitionPath);
	AVM_OS_TRACE << DECR_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

		tmpRID = aRID;
		do
		{
			aTransition = oneTransitionPath.front();

			if( fireTransition(tmpRID, aTransition) )
			{
				oneTransitionPath.pop_front();

				computeTargetMachine(tmpRID, aTransition->getCode());
			}
			else
			{
				break;
			}
		}
		while( oneTransitionPath.nonempty() );

		if( oneTransitionPath.empty() )
		{
			return( true );
		}
		else if( allTransitionPaths.empty() )
		{
			return( false );
		}

		// BACKTRACK
		else
		{
			mTraceElement.resize( saveTraceElementSize );
		}
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computePathToInput(
		const RuntimeID & aRID, InstanceOfPort * anInputTrace)
{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "computePathToInput :> " << std::endl;
	AVM_OS_TRACE << TAB2 << "Expected Input :> " << anInputTrace->getFullyQualifiedNameID() << std::endl;
	AVM_OS_TRACE << TAB2 << "Emit Output :>"; mEmitOutput.toStream(AVM_OS_TRACE);
	AVM_OS_TRACE << TAB << "end //computePathToInput" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )


	ExecutableForm * tmpExecutable = NULL;
	RuntimeID srcRID;

	// Parcourir tous les états et repérer ceux contenant les bons output/outputTo
	TableOfRuntimeT::const_iterator itRF = mED->getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = mED->getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF )
	{
		srcRID = (*itRF)->getRID();
		tmpExecutable = srcRID.getExecutable();

		if( mTableOfRuntimeStatus.isSuspended(srcRID.getOffset()) )
		{
			//!! Exclude machine
		}
		else if( mED->isIdleOrRunning( srcRID ) &&
			tmpExecutable->getForwardReachableTransition().nonempty() )
		{
			ListOfAvmTransition::const_iterator itTrans =
					tmpExecutable->getForwardReachableTransition().begin();
			ListOfAvmTransition::const_iterator endTrans =
					tmpExecutable->getForwardReachableTransition().end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( (*itTrans)->getOutputCom().contains(anInputTrace) )
				{
AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "found Output in :> " << srcRID.strUniqId() << " |==> "
			<< (*itTrans)->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

					if( tmpExecutable != (*itTrans)->getExecutable() )
					{
						if( computePathFromRunnable(srcRID, (*itTrans)) )
						{
							return( true );
						}
					}
					else if( fireTransition(srcRID, (*itTrans)) )
					{
						return( true );
					}
				}
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "Unfound Input :> " << anInputTrace->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computePathToTransition(
		const RuntimeID & aRID, AvmTransition * aTransition,
		ListOfAvmTransition & oneTransitionPath)
{
	anyTransitionPaths.clear();

	outgoingTransitions.clear();
	tgtInstance = NULL;

	// Initialization step
	fwdMachine = aRID.getExecutable();
	fwdMachine->getOutgoingTransition( outgoingTransitions );

	tgtMachine = fwdMachine;

	itTrans = outgoingTransitions.begin();
	endTrans = outgoingTransitions.end();
	for( ; itTrans != endTrans ; ++itTrans )
	{
		if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
		{
			tgtMachine = tgtInstance->getExecutable();

			if( tgtMachine->containsForwardReachableTransition(aTransition) )
			{
				anyTransitionPaths.append( ListOfAvmTransition(*itTrans) );
			}
		}
	}


	aTransitionPath.clear();

	// Iterative step
	while( anyTransitionPaths.nonempty() )
	{
		aTransitionPath.clear();
		aTransitionPath.splice( anyTransitionPaths.front() );
		anyTransitionPaths.pop_front();

		tgtInstance = aTransitionPath.back()->getTransitionTarget();
		if( tgtInstance == NULL )
		{
			continue;
		}

		fwdMachine = tgtInstance->getExecutable();
		if( fwdMachine->getTransition().contains(aTransition) )
		{
			oneTransitionPath.splice( aTransitionPath );
			oneTransitionPath.push_back( aTransition );

			return( true );
		}
		else
		{
			outgoingTransitions.clear();
			fwdMachine->getOutgoingTransition( outgoingTransitions );

			itTrans = outgoingTransitions.begin();
			endTrans = outgoingTransitions.end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( not aTransitionPath.contains( *itTrans ) )
				{
					if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
					{
						tgtMachine = tgtInstance->getExecutable();

						if( tgtMachine->containsForwardReachableTransition(aTransition) )
						{
							if( (aTransitionPath.size() < mComputingPathSizeLimit) &&
								(anyTransitionPaths.size() < mComputingPathCountLimit) )
							{
								anyTransitionPaths.push_back( aTransitionPath );
								anyTransitionPaths.back().push_back( *itTrans );
							}
						}
					}
				}
			}
		}
	}

	return( false );
}


bool AvmCoverageDirectiveTraceBuilder::computePathToTransition(
		const RuntimeID & aRID, AvmTransition * aTransition,
		ListOfListOfAvmTransition & allTransitionPaths)
{
	anyTransitionPaths.clear();
	prefixLoopTransitionPaths.clear();

	aTransitionPath.clear();

	outgoingTransitions.clear();
	tgtInstance = NULL;

	// Initialization step
	fwdMachine = aRID.getExecutable();
	fwdMachine->getOutgoingTransition( outgoingTransitions );

	tgtMachine = fwdMachine;

	itTrans = outgoingTransitions.begin();
	endTrans = outgoingTransitions.end();
	for( ; itTrans != endTrans ; ++itTrans )
	{
		if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
		{
			tgtMachine = tgtInstance->getExecutable();

			if( tgtMachine->containsForwardReachableTransition(aTransition) )
			{
				anyTransitionPaths.append( ListOfAvmTransition(*itTrans) );
			}
		}
	}

	// Iterative step
	while( anyTransitionPaths.nonempty() )
	{
//		AVM_OS_TRACE << TAB << "TMP found paths :> " << std::endl;
//		ListOfListOfAvmTransition::const_iterator itList = allTransitionPaths.begin();
//		ListOfListOfAvmTransition::const_iterator endList = allTransitionPaths.end();
//		for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//		{
//			AVM_OS_TRACE << TAB << "Path number :" << number << ">"
//					<< std::endl << INCR_INDENT;
//			AvmTransition::toStream(AVM_OS_TRACE, *itList);
//			AVM_OS_TRACE << std::endl << DECR_INDENT;
//		}
//
//		AVM_OS_TRACE << TAB << "TMP Computing paths :> " << std::endl;
//		itList = anyTransitionPaths.begin();
//		endList = anyTransitionPaths.end();
//		for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//		{
//			AVM_OS_TRACE << TAB << "Path number :" << number << ">"
//					<< std::endl << INCR_INDENT;
//			AvmTransition::toStream(AVM_OS_TRACE, *itList);
//			AVM_OS_TRACE << DECR_INDENT;
//		}
//		AVM_OS_TRACE << std::endl;

		aTransitionPath.clear();
		aTransitionPath.splice( anyTransitionPaths.front() );
		anyTransitionPaths.pop_front();

		tgtInstance = aTransitionPath.back()->getTransitionTarget();
		if( tgtInstance == NULL )
		{
			continue;
		}

		fwdMachine = tgtInstance->getExecutable();
		if( fwdMachine->getTransition().contains(aTransition) )
		{
			allTransitionPaths.push_back( aTransitionPath );
			allTransitionPaths.back().push_back( aTransition );
		}
		else
		{
			outgoingTransitions.clear();
			fwdMachine->getOutgoingTransition( outgoingTransitions );

			itTrans = outgoingTransitions.begin();
			endTrans = outgoingTransitions.end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( aTransitionPath.contains( *itTrans ) )
				{
					prefixLoopTransitionPaths.push_back( aTransitionPath );
					prefixLoopTransitionPaths.back().push_back( *itTrans );
				}
				else
				{
					if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
					{
						tgtMachine = tgtInstance->getExecutable();

						if( tgtMachine->containsForwardReachableTransition(aTransition) )
						{
							if( (aTransitionPath.size() < mComputingPathSizeLimit) &&
								(anyTransitionPaths.size() < mComputingPathCountLimit) )
							{
								anyTransitionPaths.push_back( aTransitionPath );
								anyTransitionPaths.back().push_back( *itTrans );
							}
						}
					}
				}
			}
		}
	}

AVM_IF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )
	AVM_OS_TRACE << TAB << "List of found paths :> " << std::endl;
	ListOfListOfAvmTransition::const_iterator itList = allTransitionPaths.begin();
	ListOfListOfAvmTransition::const_iterator endList = allTransitionPaths.end();
	for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
	{
		AVM_OS_TRACE << TAB << "Path number :" << number << " --> "
				<< aTransition->getFullyQualifiedNameID() << std::endl << INCR_INDENT;
		AvmTransition::toStream(AVM_OS_TRACE, *itList);
		AVM_OS_TRACE << std::endl << DECR_INDENT;
	}

//	AVM_OS_TRACE << TAB << "List of found prefix-paths :> " << std::endl;
//	itList = prefixLoopTransitionPaths.begin();
//	endList = prefixLoopTransitionPaths.end();
//	for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//	{
//		AVM_OS_TRACE << TAB << "Prefix number :" << number << "> "
//				<< std::endl << INCR_INDENT;
//		AvmTransition::toStream(AVM_OS_TRACE, *itList);
//		AVM_OS_TRACE << std::endl << DECR_INDENT;
//	}
AVM_ENDIF_DEBUG_LEVEL_FLAG2( HIGH , PROCESSOR , TRANSITION )

	return( allTransitionPaths.nonempty() );
}


void AvmCoverageDirectiveTraceBuilder::computeTargetMachine(
		RuntimeID & aRID, AvmCode * aCode)
{

	switch( aCode->getAvmOpCode() )
	{
		case AVM_OPCODE_ENABLE_INVOKE:
		case AVM_OPCODE_ENABLE_SET:
		{
			const BF & targetMachine = aCode->first();

			if( targetMachine.is< InstanceOfMachine >() )
			{
				if( (targetMachine.to_ptr< InstanceOfMachine >() !=
					aRID.getInstance()) && mED->getRuntime(aRID).hasChild() )
				{
					aRID = mED->getRuntimeFormChild(aRID,
							targetMachine.to_ptr< InstanceOfMachine >() );
				}
			}
			else if( targetMachine.is< RuntimeID >() )
			{
				aRID = targetMachine.bfRID();
			}

			break;
		}
		case AVM_OPCODE_DISABLE_SELF:
		{
			aRID = aRID.getPRID();

			break;
		}
		case AVM_OPCODE_DISABLE_SELVES:
		{
			if( aCode->first().isInteger() )
			{
				for( avm_uinteger_t level = aCode->first().toInteger() ;
						level > 0 ; --level )
				{
					aRID = aRID.getPRID();
				}
			}
			else
			{
				aRID = aRID.getPRID();
			}

			break;
		}
		default:
		{
			if( StatementTypeChecker::isSchedule(aCode) )
			{
				AvmCode::const_iterator it = aCode->begin();
				AvmCode::const_iterator endIt = aCode->end();
				for( ; it != endIt ; ++it )
				{
					if( (*it).is< AvmCode >() )
					{
						computeTargetMachine(aRID, (*it).to_ptr< AvmCode >());
					}
				}
			}
			break;
		}
	}
}


} /* namespace sep */
