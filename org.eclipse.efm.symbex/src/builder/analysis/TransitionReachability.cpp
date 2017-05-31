/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 10 nov. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "TransitionReachability.h"


#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/AvmTransition.h>
#include <fml/executable/ExecutableLib.h>

#include <fml/expression/StatementTypeChecker.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/Message.h>
#include <fml/runtime/RuntimeForm.h>
#include <fml/runtime/RuntimeID.h>

#include <fml/trace/TracePoint.h>
#include <fml/trace/TraceSequence.h>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
TransitionReachability::TransitionReachability(const ExecutionContext & anEC,
		const RuntimeID & aRID, AvmTransition * aTransition)
: theEC( anEC ),
theED( anEC.refExecutionData() ),
theRID( aRID ),
theTransition( aTransition ),
theTransitionPoint( NULL ),
theTraceElement( ),

theRuntimePathComputingCountLimit( 16 ),

theGoalAchievedFlag( false ),

theVirtualBuffer(theTransition, NULL, 0, TYPE_LIFO_SPECIFIER, -1),
theEmitOutput( & theVirtualBuffer ),

theTableOfRuntimeStatus( *( theED.getRuntimeFormStateTable() ) )
{
	//!! NOTHING
}


/**
 * UTILS
 */
bool TransitionReachability::initialize()
{
	theGoalAchievedFlag = false;

	if( theRID.invalid() )
	{
		if( theED.mRID.getExecutable()->getTransition().contains(theTransition) )
		{
			theRID = theED.mRID;
		}

		if( theRID.invalid() )
		{
			if( theTransitionPoint != NULL )
			{
				theTransitionPoint->updateRID( theED );

				theRID = theTransitionPoint->RID;
			}
			else
			{
				theRID = theED.getRuntimeID( theTransition->getExecutable() );
			}
		}
	}

	return( theRID.valid() );
}


bool TransitionReachability::computePath()
{
	if( initialize() )
	{
		AvmCommunicationFactory::collectBufferMessage(theED, theEmitOutput);

		return( theGoalAchievedFlag = computePath(theRID, theTransition) );
	}

	return( false );
}


bool TransitionReachability::computePath(TraceSequence & aTraceElement)
{
	if( initialize() )
	{
		AvmCommunicationFactory::collectBufferMessage(theED, theEmitOutput);

		if( computePath(theRID, theTransition) )
		{
			aTraceElement.copyTrace( theTraceElement );

			theGoalAchievedFlag = true;

			return( true );
		}
	}

	return( false );
}



void TransitionReachability::report(OutStream & os)
{
	os << "Trace to reach :> " << theTransition->strTransitionHeader();
	theTraceElement.toStream(os);

//	os << TAB << "Emit Output :>" << to_stream( theEmitOutput );

	os << ( theGoalAchievedFlag ? "NEW" : "NO" ) << " OBJECTIVE !!!" << std::endl;
}



bool TransitionReachability::computePath(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB << "computePath from :> ";
	theEC.traceMinimum(AVM_OS_COUT);
	AVM_OS_COUT << TAB2 << aRID.strUniqId() << " |==> ";
	aTransition->toStreamHeader(AVM_OS_COUT); AVM_OS_COUT << std::endl;
	if( aTransition->hasInternalCommunicationCode() )
	{
		AVM_OS_COUT << TAB2 << "com |==> ";
		BaseCompiledForm::toStreamStaticCom(AVM_OS_COUT,
				aTransition->getInternalCommunicationCode());
	}
	AVM_OS_COUT << TAB2 << "Emit Output :>" << to_stream( theEmitOutput )
			 << TAB << "end //computePath" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	if( theED.isIdleOrRunning(aRID) )
	{
		return( fireTransition(aRID, aTransition) );
	}
	else
	{
		return( computePathToTransition(aRID, aTransition) );
	}

	return( false );
}


bool TransitionReachability::fireTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl
			<< TAB << "fireTransition :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl
			<< TAB2 << "Emit Output :>" << to_stream( theEmitOutput )
			<< TAB << "end //fireTransition" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	theTableOfRuntimeStatus.stateSet(aRID.getOffset(), PROCESS_SUSPENDED_STATE);

	if( aTransition->hasInputCom() )
	{
		ListOfInstanceOfPort anInputTrace( aTransition->getInputCom() );
		if( theEmitOutput.uncontains( anInputTrace ) )
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


void TransitionReachability::traceTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
	TracePoint * tmpTP = new TracePoint(
			ENUM_TRACE_POINT::TRACE_TRANSITION_NATURE,
			AVM_OPCODE_INVOKE_TRANSITION, aRID, aTransition);

	theTraceElement.points.append( BF(tmpTP) );

	// Virtual Eval Of aTransition
	if( aTransition->hasOutputCom() )
	{
		ListOfInstanceOfPort::const_iterator itOutput =
				aTransition->getOutputCom().begin();
		ListOfInstanceOfPort::const_iterator endOutput =
				aTransition->getOutputCom().end();
		for( ; itOutput != endOutput ; ++itOutput )
		{
			theEmitOutput.push( Message(aRID, INCR_BF(*itOutput)) );
		}
	}
}


bool TransitionReachability::computePathToTransition(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl
			<< TAB << "computePathToTransition using :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	RuntimeID tmpRID = aRID.getPRID();
	for( ; tmpRID.valid() ; tmpRID = tmpRID.getPRID() )
	{
//		AVM_OS_COUT << tmpRID.strUniqId() << " : "
//				<< tmpRID.getInstance()->getFullyQualifiedNameID() << std::endl;

		if( theED.isIdleOrRunning(tmpRID) )
		{
			break;
		}
	}

	AVM_OS_ASSERT_FATAL_NULL_SMART_POINTER_EXIT( tmpRID )
			<< "Runnable Ancestor Statemachine for "
			<< aRID.strUniqId() << " in the context of "
			<< aTransition->getFullyQualifiedNameID() << " !!!"
			<< SEND_EXIT;

	const RuntimeForm & tmpRF = theED.getRuntime(tmpRID);

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB2 << "Runnable Ancestor Statemachine :> "
			<< tmpRID.str() << std::endl
			<< TAB2 << "Runnable Ancestor State Scheduler :> {";
	tmpRF.getOnSchedule()->toStreamRoutine( AVM_OS_COUT )
			<< TAB2 << "}" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	if( tmpRF.getOnSchedule()->isOpCode( AVM_OPCODE_RUN ) &&
		tmpRF.getOnSchedule()->first().is< RuntimeID >() )
	{
		return( computePathFromRunnable(
				tmpRF.getOnSchedule()->first().bfRID(), aTransition) );
	}

	return( false );
}


bool TransitionReachability::computePathFromRunnable(
		const RuntimeID & aRID, AvmTransition * aTransition)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << std::endl
			<< TAB << "computePathFromRunnable using :> " << aRID.strUniqId()
			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	if( not aRID.getExecutable()->
			containsForwardReachableTransition(aTransition) )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
		AVM_OS_COUT << TAB2 << "Unreachable transition :> "
				<< theTransition->strTransitionHeader() << std::endl
				<< TAB2 << "from : " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

		return( false );
	}


AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB << "Looking for a path to :> " << aRID.str() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	ListOfAvmTransition oneTransitionPath;

	if( computePathToTransition(aRID, aTransition, oneTransitionPath) )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << INCR_INDENT;
	AvmTransition::toStream(AVM_OS_COUT, oneTransitionPath);
	AVM_OS_COUT << DECR_INDENT << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

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

				if( not computeTargetMachine(tmpRID, aTransition->getCode()) )
				{
					return( false );
				}
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



//bool TransitionReachability::computePathFromRunnable(
//		const RuntimeID & aRID, AvmTransition * aTransition)
//{
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	AVM_OS_COUT << std::endl
//			<< TAB << "computePathFromRunnable using :> " << aRID.strUniqId()
//			<< " |==> " << aTransition->strTransitionHeader() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//
//	if( not aRID.getExecutable()->
//			containsForwardReachableTransition(aTransition) )
//	{
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//		AVM_OS_COUT << TAB2 << "Unreachable transition :> "
//				<< theTransition->strTransitionHeader() << std::endl
//				<< TAB2 << "from : " << aRID.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//
//		return( false );
//	}
//
//
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	AVM_OS_COUT << TAB << "Looking for a path to :> " << aRID.str() << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//
//
//	// All found path
//	ListOfListOfAvmTransition allTransitionPaths;
//	computePathToTransition(aRID, aTransition, allTransitionPaths);
//
//	BFList saveTracePoints( theTraceElement.points );
//
//	ListOfAvmTransition oneTransitionPath;
//	RuntimeID tmpRID;
//
////	if( computePathToTransition(aRID, aTransition, oneTransitionPath) )
//	while( allTransitionPaths.nonempty() )
//	{
//		oneTransitionPath.clear();
//		oneTransitionPath.splice( allTransitionPaths.front() );
//		allTransitionPaths.pop_front();
//
//AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//	AVM_OS_COUT << TAB << "Found Path --> "
//			<< aTransition->getFullyQualifiedNameID() << std::endl << INCR_INDENT;
//	AvmTransition::toStream(AVM_OS_COUT, oneTransitionPath);
//	AVM_OS_COUT << DECR_INDENT << std::endl;
//AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
//
//		tmpRID = aRID;
//		do
//		{
//			aTransition = oneTransitionPath.front();
//
//			if( fireTransition(tmpRID, aTransition) )
//			{
//				oneTransitionPath.pop_front();
//
//				computeTargetMachine(tmpRID, aTransition->getCode());
//			}
//			else
//			{
//				break;
//			}
//		}
//		while( oneTransitionPath.nonempty() );
//
//		if(  oneTransitionPath.empty() )
//		{
//			return( true );
//		}
//		else if( allTransitionPaths.empty() )
//		{
//			return( false );
//		}
//
//		// BACKTRACK
//		else if( saveTracePoints.empty() )
//		{
//			theTraceElement.points.clear();
//		}
//		else
//		{
//			while( theTraceElement.points.back().isNTEQ( saveTracePoints.back() ) )
//			{
//				theTraceElement.points.pop_back();
//			}
//		}
//	}
//
//	return( false );
//}


bool TransitionReachability::computePathToInput(
		const RuntimeID & aRID, InstanceOfPort * anInputTrace)
{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB << "computePathToInput :> " << std::endl
			<< TAB2 << "Expected Input :> "
			<< anInputTrace->getFullyQualifiedNameID() << std::endl
			<< TAB2 << "Emit Output :>" << to_stream( theEmitOutput )
			<< TAB << "end //computePathToInput" << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )


	ExecutableForm * tmpExecutable = NULL;
	RuntimeID srcRID;

	// Parcourir tous les états et repérer ceux contenant les bons output/outputTo
	TableOfRuntimeT::const_iterator itRF = theED.getTableOfRuntime().begin();
	TableOfRuntimeT::const_iterator endRF = theED.getTableOfRuntime().end();
	for( ; itRF != endRF ; ++itRF )
	{
		srcRID = (*itRF)->getRID();
		tmpExecutable = srcRID.getExecutable();

		if( theTableOfRuntimeStatus.isSuspended(srcRID.getOffset()) )
		{
			//!! Exclude machine
		}
		else if( theED.isIdleOrRunning( srcRID ) &&
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
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB << "found Output in :> " << srcRID.strUniqId() << " |==> "
			<< (*itTrans)->strTransitionHeader() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

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

AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )
	AVM_OS_COUT << TAB << "Unfound Input :> "
			<< anInputTrace->getFullyQualifiedNameID() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRANSITION )

	return( false );
}


bool TransitionReachability::computePathToTransition(const RuntimeID & aRID,
		AvmTransition * aTransition, ListOfAvmTransition & oneTransitionPath)
{
	ListOfListOfAvmTransition anyTransitionPaths;

	ListOfAvmTransition listOfOutgoingTransition;
	InstanceOfMachine * tgtInstance;

	// Initialization step
	ExecutableForm * fwdMachine = aRID.getExecutable();
	fwdMachine->getOutgoingTransition( listOfOutgoingTransition );

	ExecutableForm * tgtMachine = fwdMachine;

	ListOfAvmTransition::const_iterator itTrans = listOfOutgoingTransition.begin();
	ListOfAvmTransition::const_iterator endTrans = listOfOutgoingTransition.end();
	for( ; itTrans != endTrans ; ++itTrans )
	{
		if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
		{
			tgtMachine = tgtInstance->getExecutable();
		}
		if( tgtMachine->containsForwardReachableTransition(aTransition) )
		{
			anyTransitionPaths.append( ListOfAvmTransition(*itTrans) );
		}
	}


	ListOfAvmTransition aTransitionPath;

	// Iterative step
	while( anyTransitionPaths.nonempty() )
	{
		aTransitionPath.clear();
		aTransitionPath.splice( anyTransitionPaths.front() );
		anyTransitionPaths.pop_front();

		if( (tgtInstance = aTransitionPath.back()->getTransitionTarget()) != NULL )
		{
			fwdMachine = tgtInstance->getExecutable();
		}
		if( fwdMachine->getTransition().contains(aTransition) )
		{
			oneTransitionPath.splice( aTransitionPath );
			oneTransitionPath.push_back( aTransition );

			return( true );
		}
		else
		{
			listOfOutgoingTransition.clear();
			fwdMachine->getOutgoingTransition( listOfOutgoingTransition );

			itTrans = listOfOutgoingTransition.begin();
			endTrans = listOfOutgoingTransition.end();
			for( ; itTrans != endTrans ; ++itTrans )
			{
				if( not aTransitionPath.contains( *itTrans ) )
				{
					if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
					{
						tgtMachine = tgtInstance->getExecutable();
					}
					if( tgtMachine->containsForwardReachableTransition(aTransition) )
					{
						if( anyTransitionPaths.size() <
							theRuntimePathComputingCountLimit )
						{
							anyTransitionPaths.push_back( aTransitionPath );
							anyTransitionPaths.back().push_back( *itTrans );
						}
					}
				}
			}
		}
	}

	return( false );
}


bool TransitionReachability::computePathToTransition(const RuntimeID & aRID,
		AvmTransition * aTransition, ListOfListOfAvmTransition & allTransitionPaths)
{
	ListOfListOfAvmTransition anyTransitionPaths;
	ListOfListOfAvmTransition prefixLoopTransitionPaths;

	ListOfAvmTransition aTransitionPath;

	ListOfAvmTransition listOfOutgoingTransition;
	InstanceOfMachine * tgtInstance;

	// Initialization step
	ExecutableForm * fwdMachine = aRID.getExecutable();
	fwdMachine->getOutgoingTransition( listOfOutgoingTransition );

	ExecutableForm * tgtMachine = fwdMachine;

	ListOfAvmTransition::const_iterator itTrans = listOfOutgoingTransition.begin();
	ListOfAvmTransition::const_iterator endTrans = listOfOutgoingTransition.end();
	for( ; itTrans != endTrans ; ++itTrans )
	{
		if( (tgtInstance = (*itTrans)->getTransitionTarget()) != NULL )
		{
			tgtMachine = tgtInstance->getExecutable();
		}
		if( tgtMachine->containsForwardReachableTransition(aTransition) )
		{
			anyTransitionPaths.append( ListOfAvmTransition(*itTrans) );
		}
	}

	// Iterative step
	while( anyTransitionPaths.nonempty() )
	{
//		AVM_OS_COUT << TAB << "TMP found paths :> " << std::endl;
//		ListOfListOfAvmTransition::const_iterator itList = allTransitionPaths.begin();
//		ListOfListOfAvmTransition::const_iterator endList = allTransitionPaths.end();
//		for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//		{
//			AVM_OS_COUT << TAB << "Path number :" << number << ">"
//					<< std::endl << INCR_INDENT;
//			AvmTransition::toStream(AVM_OS_COUT, *itList);
//			AVM_OS_COUT << std::endl << DECR_INDENT;
//		}
//
//		AVM_OS_COUT << TAB << "TMP Computing paths :> " << std::endl;
//		itList = anyTransitionPaths.begin();
//		endList = anyTransitionPaths.end();
//		for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//		{
//			AVM_OS_COUT << TAB << "Path number :" << number << ">"
//					<< std::endl << INCR_INDENT;
//			AvmTransition::toStream(AVM_OS_COUT, *itList);
//			AVM_OS_COUT << DECR_INDENT;
//		}
//		AVM_OS_COUT << std::endl;

		aTransitionPath.clear();
		aTransitionPath.splice( anyTransitionPaths.front() );
		anyTransitionPaths.pop_front();

		if( (tgtInstance = aTransitionPath.back()->getTransitionTarget()) != NULL )
		{
			fwdMachine = tgtInstance->getExecutable();
		}
		if( fwdMachine->getTransition().contains(aTransition) )
		{
			allTransitionPaths.push_back( aTransitionPath );
			allTransitionPaths.back().push_back( aTransition );
		}
		else
		{
			listOfOutgoingTransition.clear();
			fwdMachine->getOutgoingTransition( listOfOutgoingTransition );

			itTrans = listOfOutgoingTransition.begin();
			endTrans = listOfOutgoingTransition.end();
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
					}
					if( tgtMachine->containsForwardReachableTransition(aTransition) )
					{
						anyTransitionPaths.push_back( aTransitionPath );
						anyTransitionPaths.back().push_back( *itTrans );
					}
				}
			}
		}
	}

	AVM_OS_COUT << TAB << "List of found paths :> " << std::endl;
	ListOfListOfAvmTransition::const_iterator itList = allTransitionPaths.begin();
	ListOfListOfAvmTransition::const_iterator endList = allTransitionPaths.end();
	for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
	{
		AVM_OS_COUT << TAB << "Path number :" << number << " --> "
				<< aTransition->getFullyQualifiedNameID() << std::endl << INCR_INDENT;
		AvmTransition::toStream(AVM_OS_COUT, *itList);
		AVM_OS_COUT << std::endl << DECR_INDENT;
	}

//	AVM_OS_COUT << TAB << "List of found prefix-paths :> " << std::endl;
//	itList = prefixLoopTransitionPaths.begin();
//	endList = prefixLoopTransitionPaths.end();
//	for( avm_size_t number = 0 ; itList != endList ; ++itList , ++number )
//	{
//		AVM_OS_COUT << TAB << "Prefix number :" << number << ">"
//				<< std::endl << INCR_INDENT;
//		AvmTransition::toStream(AVM_OS_COUT, *itList);
//		AVM_OS_COUT << std::endl << DECR_INDENT;
//	}

	return( allTransitionPaths.nonempty() );
}


bool TransitionReachability::computeTargetMachine(
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
				if( (targetMachine.to_ptr< InstanceOfMachine >()
						!= aRID.getInstance())
					&& theED.getRuntime(aRID).hasChild() )
				{
					aRID = theED.getRuntimeFormChild(aRID,
							targetMachine.to_ptr< InstanceOfMachine >() );
				}
			}
			else if( targetMachine.is< RuntimeID >() )
			{
				aRID = targetMachine.bfRID();
			}

			return( true );
		}
		case AVM_OPCODE_DISABLE_SELF:
		{
			aRID = aRID.getPRID();

			return( true );
		}
		case AVM_OPCODE_DISABLE_INVOKE:
		{
			if( (aCode->first() == ExecutableLib::MACHINE_SELF)
				|| (aRID == aCode->first()) )
			{
				aRID = aRID.getPRID();

				return( true );
			}
			else
			{
				return( false );
			}
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

			return( true );
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
						if( not computeTargetMachine(aRID,
								(*it).to_ptr< AvmCode >()) )
						{
							return( false );
						}
					}
				}
			}

			return( true );
		}
	}
}


} /* namespace sep */
