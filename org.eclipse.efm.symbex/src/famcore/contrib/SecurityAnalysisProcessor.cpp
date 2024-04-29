/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: mai. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SecurityAnalysisProcessor.h"

#include <builder/Builder.h>

#include <common/BF.h>

#include <computer/primitive/AvmCommunicationFactory.h>

#include <fml/executable/InstanceOfData.h>

#include <fml/template/TimedMachine.h>
#include <fml/runtime/ExecutionConfiguration.h>
#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>

#include <fml/workflow/WObject.h>
#include <fml/workflow/Query.h>

#include <famcore/queue/ExecutionQueue.h>

#include <sew/Configuration.h>

#include <solver/api/SolverFactory.h>


namespace sep
{


/**
 * CONSTRUCTOR
 * Default
 */
SecurityAnalysisProcessor::SecurityAnalysisProcessor(
		SymbexControllerUnitManager & aControllerUnitManager,
		const WObject * wfParameterObject)
: RegisteredProcessorUnit(aControllerUnitManager ,
		wfParameterObject, AVM_PREPOST_FILTERING_STAGE),
theAttackSequenceTransitionNameVector( ),
theAttackSequenceTransitionVector( ),
//theTimedVarsVector( ),
theVerdict( ),
theVerdictEmited( false ),
//theTimeVarInstance( ),
theLeavesECVector( ),
//timeReferenceInstance( ),
theErasedNodes( 0 ),
theKActions( -1 ),
theSwdMachineName( ),
theAttMachineName( ),
theMainExecutionData(  getConfiguration().getMainExecutionData()  )
{
	//!! NOTHING
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE API
////////////////////////////////////////////////////////////////////////////////

bool SecurityAnalysisProcessor::configureImpl()
{
	// NEW: we stop as soon as we find a fail
	theVerdict = "PASS (try covering more paths to be sure)";
	theErasedNodes = 0;
	theVerdictEmited = false;

	/* WILL WE HANDLE TIME??
	const WObject * theTimeHandling =
			Query::getWSequence(mParameterWObject , "TIME_HANDLING");

	if( TimedMachine::SYSTEM_VAR_DELTA_TIME != nullptr )
	{
		ExecutableSystem * anExecutableSystem =
				getConfiguration().getExecutableSystem();

		ExecutableQuery XQuery( getConfiguration() );

		timeReferenceInstance = XQuery.getDataByAstElement(
				TimedMachine::SYSTEM_VAR_GLOBAL_TIME );

		theTimeVarInstance = XQuery.getDataByAstElement(
				TimedMachine::SYSTEM_VAR_DELTA_TIME );
	}
	else
	{
		std::string theCurrentTimeVar =
				Query::getWPropertyString(theTimeHandling, "currentTime", "");
		std::string timeVar =
				Query::getWPropertyString(theTimeHandling, "timeVar", "");
		timeReferenceInstance = ENV.getBuilder().searchSymbolData(
				theMainExecutionData, theCurrentTimeVar);
		if( timeReferenceInstance.invalid() )
		{
			AVM_OS_LOG << "Unfound currentTime< " << theCurrentTimeVar
					<< "> parameter!" << std::endl;

			theConfigFlag = false;
		}
		theTimeVarInstance = ENV.getBuilder().searchSymbolData(
				theMainExecutionData, timeVar);
		if( theTimeVarInstance.invalid() )
		{
			AVM_OS_LOG << "Unfound timeVar < " << timeVar << "> parameter!"
					<< std::endl;

			theConfigFlag = false;
		}
	}
	 */

	const WObject * theConfiguration =
			Query::getWSequence(mParameterWObject , "PROPERTY");
	if( theConfiguration != WObject::_NULL_ )
	{
		theKActions= -1;
		theSwdMachineName = "", theAttMachineName= "";

		WObject::const_iterator itWfO = theConfiguration->owned_begin();
		WObject::const_iterator endWfO = theConfiguration->owned_end();
		for( ; itWfO != endWfO ; ++itWfO )
		{
			if( (*itWfO)->isWProperty() )
			{
				AVM_OS_LOG << "Workflow-Property is : "
						<< (*itWfO)->toString();

				if ( (*itWfO)->getNameID() == "k" )
				{
					theKActions = (*itWfO)->getIntegerValue();
				}

				if( (*itWfO)->getNameID() == "swdMachineName" )
				{
					theSwdMachineName = (*itWfO)->toStringValue();
				}
				if( (*itWfO)->getNameID() == "k" )
				{
					theAttMachineName = (*itWfO)->toStringValue();
				}
			}
		}
		if( (theKActions==-1)
			|| theSwdMachineName.empty()
			|| theAttMachineName.empty() )
		{
			AVM_OS_WARN << "Unfound parameter k or "
					"theSwdMachineName or attMachineName" << std::endl;

			mConfigFlag = false;
		}
	}
	else
	{
		// ERROR MESSAGE
		mConfigFlag = false;
	}

	mConfigFlag = initSequenceOfTransitions(
			theAttackSequenceTransitionNameVector,
			theAttackSequenceTransitionVector,
			"ATTACK_TRANSITIONS_LIST");

	mConfigFlag = initSequenceOfTransitions(theWarningsTransitionNameVector,
			theWarningsTransitionVector,
			"WARNING_TRANSITIONS_LIST");

	return mConfigFlag;
}

bool SecurityAnalysisProcessor::initSequenceOfTransitions(
		VectorOfString & namesVector,
		VectorOfAvmTransition & avmTransitionsVector,
		const std::string & sectionName)
{
	// Initialisation de namesVector avec la liste de noms de transition
	// contenue dans le fichier favm
	const WObject * theSECTION = Query::getWSequence(getParameterWObject() , sectionName);
	Query::getWPropertyString(theSECTION, "transition", namesVector);

	// Initialisation de theAttackSequenceTransitionNameVector et theAttackSequenceTransitionVector
	AvmTransition * aTransition;

	for( std::size_t index = 0 ; index < namesVector.size() ; ++index )
	{
		aTransition = nullptr;

		TableOfExecutableForm::const_raw_iterator itExec =
			getConfiguration().getExecutableSystem().getExecutables().begin();
		TableOfExecutableForm::const_raw_iterator endExec =
			getConfiguration().getExecutableSystem().getExecutables().end();
		for( ; itExec != endExec ; ++itExec )
		{
			aTransition = (itExec)->getTransition().rawByQualifiedNameID(
					namesVector[index], NamedElement::OP_ANY_COMPARER);

			if( aTransition != nullptr )
			{
				avmTransitionsVector.append( aTransition );

				break;
			}

//	bool notFound;
//	for( std::size_t index = 0 ; index < namesVector.size() ; ++index )
//	{
//		notFound = true;
//		TableOfExecutableForm::raw_iterator it =
//				getConfiguration().getExecutableSystem().begin();
//		TableOfExecutableForm::raw_iterator endIt =
//				getConfiguration().getExecutableSystem().end();
//		for( ; (itExec != endIt) && notFound  ; ++it )
//		{
//			TableOfAvmTransition::iterator itProg = (*it)->getTransition().begin();
//			for( ; itProg != (*it)->getTransition().end() ; ++itProg )
//			{
//				if( (*itProg)->isScopeTransition() )
//				{
//					if( (*itProg)->safeAstElement().isEqualsID(
//						namesVector[index], NamedElement::OP_ANY_COMPARER) )
//					{
//						avmTransitionsVector.append( *itProg );
//
//						notFound = false;
//						break;
//					}
//				}
//			}
		}
		if( aTransition == nullptr )
		{
			AVM_OS_WARN << "ERROR: SecurityAnalysisFilter::initSequenceOfTransitions !"
					<< std::endl
					<< "==> Transition " << namesVector[index]
					<< " not found in the specification." << std::endl << std::endl;
			return false;
		}
	}

	return true;
}

////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void SecurityAnalysisProcessor::reportDefault(OutStream & os) const
{
	reportHeader(os, "AVM SECURITY ANALYSIS ");

	os << EMPHASIS( ("THE EMITTED VERDICT IS : " + theVerdict), '=', 50 );
}



////////////////////////////////////////////////////////////////////////////////
// PRE-PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool SecurityAnalysisProcessor::preprocess()
{
	return( true );
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool SecurityAnalysisProcessor::prefilter()
{
	// On appelle la méthode preEval de la classe mère :
	//		appel des preFilter sur les EC dans Ready
	if( not AbstractProcessorUnit::prefilter() )
	{
	}

	return( getExecutionQueue().hasReady() );
}

bool SecurityAnalysisProcessor::prefilter(ExecutionContext & anEC)
{
	VectorOfAvmTransition observedSequenceVector;
	avm_integer_t localK;
	SECURITY_ANALYSIS_MARK analyzedMark;

	SecurityAnalysisProcessorInfo * currentSecurityAnalysisInfo = nullptr;
	SecurityAnalysisProcessorInfo * previousSecurityAnalysisInfo = nullptr;

	if (theVerdictEmited==true)
	{
		// we found a non robust path, so we can stop the execution!!
		return false;
	}

	if (anEC.hasPrevious())
	{
		// Get localK of previous (parent)
		if (anEC.getPrevious()->hasInformation())
		{
			previousSecurityAnalysisInfo = anEC.getPrevious()->getInformation()
					->getUniqSpecificInfo< SecurityAnalysisProcessorInfo >();

			localK = previousSecurityAnalysisInfo->getLocalK();
			observedSequenceVector = previousSecurityAnalysisInfo->getObservedSequence();
			analyzedMark = previousSecurityAnalysisInfo->getTheAnalyzedMark();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Its previous EC: " << anEC.getPrevious()->str_min() << std::endl
			<< "Its previous observed sequence size is: "
			<< previousSecurityAnalysisInfo->getObservedSequence().size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		}
		else
		{
			// setting ??
			previousSecurityAnalysisInfo =
					anEC.getPrevious()->getUniqInformation()
					->getUniqSpecificInfo< SecurityAnalysisProcessorInfo >();
		}
	}

	currentSecurityAnalysisInfo = anEC.getUniqInformation()
			->getUniqSpecificInfo< SecurityAnalysisProcessorInfo >();

	if((anEC.getHeight() <= 0)){
		observedSequenceVector.clear();
		currentSecurityAnalysisInfo->setObservedSequence(observedSequenceVector);
		currentSecurityAnalysisInfo->setLocalK(theKActions);
		currentSecurityAnalysisInfo->setTheAnalyzedMark(NOT_MARKED);

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Root, initializing, assigning and skipping: " << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		return true;
	}


	if( (previousSecurityAnalysisInfo->isMarked() == true))
	{

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Robustness already computed for this path!!!! for EC: "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	currentSecurityAnalysisInfo->setObservedSequence(
			previousSecurityAnalysisInfo->getObservedSequence());

	currentSecurityAnalysisInfo->setLocalK(
			previousSecurityAnalysisInfo->getLocalK());

	currentSecurityAnalysisInfo->setTheAnalyzedMark(
			previousSecurityAnalysisInfo->getTheAnalyzedMark());

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "Assigning and skipping EC: " << anEC.str_min() << std::endl
		<< "Local observed sequence size : "
		<< currentSecurityAnalysisInfo->getObservedSequence().size() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		return true;
	}

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "The local observed sequence size is: " << std::endl
			<< currentSecurityAnalysisInfo->getObservedSequence().size() << std::endl;

	AVM_OS_COUT << "SecurityAnalysisProcessor::prefilter(...) EC:> "
			<< anEC.str_min() << std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )


	if( anEC.hasRunnableElementTrace() )
	{
		if( recursiveAnalyseElement(anEC.getRunnableElementTrace(),
				observedSequenceVector, localK, analyzedMark) )
		{
AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_LOG << "An action of the attacker was detected:" << anEC.getIdNumber()
		<< " now the observed sequence size is = " << std::endl
		<< currentSecurityAnalysisInfo->getObservedSequence().size() << std::endl
		<< " and the localK is " << localK << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
		}

		currentSecurityAnalysisInfo->setObservedSequence(observedSequenceVector);
		currentSecurityAnalysisInfo->setLocalK(localK);
		currentSecurityAnalysisInfo->setTheAnalyzedMark(analyzedMark);

		return true;

	}

	return true;
}

bool SecurityAnalysisProcessor::recursiveAnalyseElement(const BF & aBF,
		VectorOfAvmTransition & observedSequenceVector,
		avm_integer_t & localK,
		SECURITY_ANALYSIS_MARK & analyzedMark)
{
	// Cas AvmCode
	if( aBF.is< AvmCode >() )
	{
		for( const auto & itOperand : aBF.to< AvmCode >().getOperands() )
		{
			if ( recursiveAnalyseElement( itOperand,
					observedSequenceVector, localK, analyzedMark) )
			{
				return true;
			}
		}
		return false;
	}
	else if( aBF.is< ExecutionConfiguration >() )
	{
		const ExecutionConfiguration & anExecutionConf = aBF.to< ExecutionConfiguration >();
		if( theAttackSequenceTransitionVector.contains(anExecutionConf.getTransition()) )
		{
AVM_IF_DEBUG_FLAG( PROCESSOR )
	AVM_OS_LOG << "An action of the attacker is being performed!" << std::endl;
	anExecutionConf.toTransition().toStream(AVM_OS_LOG);
	AVM_OS_LOG << " and the localK is " << localK << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
			// it is a transition from the attacker.
			// have we seen it before? (loops)
			if( not observedSequenceVector.contains(anExecutionConf.getTransition()) )
			{
				// is a non observed action from the attacker. add it
				localK--;
				observedSequenceVector.push_back(anExecutionConf.getTransition());
				// analyze robustness
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "It is not repeated!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )

				if (localK <0)
				{
					// the attacker has performed k+1 actions and it hasn't been detected
					// --> mark as not robust!!
					analyzedMark = NOT_ROBUST;
					theVerdictEmited = true;
					theVerdict = "FAIL";
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "--->>> marking as NOT ROBUST! the execution will STOP!!!!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				}
				return true;
			}
			else
			{
				// it is a repeated attacker action: do nothing ?
				// TODO: we can set a bound on the number of times we allow to see
				// a repeated transition
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "Repeated, do nothing!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				return false;
			}
		}
		else if( theWarningsTransitionVector.contains(anExecutionConf.getTransition()) )
		{
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "An action of the SWD is being performed!" << std::endl;
anExecutionConf.toTransition().toStream(AVM_OS_LOG);
AVM_OS_LOG << " and the localK is " << localK
	<< std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
			// it is a transition from the swd.
			// analyze if it happens before k actions
			if( localK >= 0 )
			{
				// it is robust
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "It is robust for this branch!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				analyzedMark = ROBUST;
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "--->>> marking as ROBUST!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				return true;
			}
			else
			{
				// it the warning came too late
				// this should never happen, since this case is supposed to be detected before
AVM_IF_DEBUG_FLAG( PROCESSOR )
AVM_OS_LOG << "WARNING in SecurityAnalysisProcessor::recursiveAnalyseElement: warning after k actions?!" << std::endl;
AVM_ENDIF_DEBUG_FLAG( PROCESSOR )
				return false;
			}
		}
	}
	return false;
}

////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool SecurityAnalysisProcessor::postfilter()
{
	ecQueue = &( getExecutionQueue().getResultQueue() );
	ecQueueIt = ecQueue->begin();
	ecQueueItEnd = ecQueue->end();
	for( ; ecQueueIt != ecQueueItEnd ; )
	{
		if( not postfilter(* (*ecQueueIt)) )
			{
			AVM_OS_LOG << "FAIL in postfilter security analysis!"
					<< std::endl;
			return false;
			}
		else
		{
			++ecQueueIt;
		}
	}
	return (getExecutionQueue().hasResult());
}

bool SecurityAnalysisProcessor::postfilter(ExecutionContext &anEC)
{
	if(anEC.getHeight() <= 0)
	{
		return true;
	}

	/* (WILL WE HANDLE TIME?)
	SecurityAnalysisProcessorInfo * currentSecurityAnalysisInfo =
			anEC.getUniqInformation()->getUniqSecurityAnalysisProcessorInfo();

	// set THIS current time (since it is not a tau, nor it was projected)
	const BF & referenceTimeVar = ENV.getRvalue(anEC.getExecutionData(),
			anEC.getExecutionData().getSystemRID(), timeReferenceInstance);
	currentSecurityAnalysisInfo->setTimeReference(referenceTimeVar);
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << "2. Setting time reference to "
			<< referenceTimeVar.str()
			<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
*/
	return( true );
}

////////////////////////////////////////////////////////////////////////////////
// POST-PROCESS API
////////////////////////////////////////////////////////////////////////////////

void SecurityAnalysisProcessor::searchLeavesWithPositiveK(ExecutionContext * anEC)
{
	if( anEC->isLeafNode() && anEC->isnotRoot() )
	{
		// it is a leaf, take its parent (the last leave is not evaluated by the filters)
		if (!theLeavesECVector.contains(anEC->getPrevious()))
		{
			if (anEC->getPrevious()->getUniqInformation()
					->getUniqSpecificInfo< SecurityAnalysisProcessorInfo >()
					->getLocalK() > 0)
			{
				theLeavesECVector.append( anEC->getPrevious() );
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			AVM_OS_LOG << "LEAF!!! local k is : "
					<< anEC->getPrevious()->getUniqInformation()
					->getUniqSpecificInfo< SecurityAnalysisProcessorInfo >()
					->getLocalK()
					<< " => the EC: " << anEC->getPrevious()->str_min()
					<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
			}
		}
	}
	else
	{
		// recursive lookup
		for( const auto & itChildEC : anEC->getChildContexts() )
		{
			searchLeavesWithPositiveK( itChildEC );
		}
	}
}



bool SecurityAnalysisProcessor::postprocess()
{
/*
	theLeavesECVector.clear();
	// search the leaves of the paths in which the attacker intervened
	searchLeavesWithPositiveK( MainDataConfiguration::getInstance()->getFirstExecutionTrace() );
	if( theLeavesECVector.empty() )
	{
		AVM_OS_LOG << "ZERO LEAVE :> FAILED !" << std::endl;
		theVerdict = "FAILED";
		return( true );
	}

	// check for the mark in the paths
	// for the moment, if a path has no mark, we assume that it is
	// because there was a loop or something, so we say nothing
	// TODO: study what to do if there is no mark
	SecurityAnalysisProcessorInfo * securityAnalysisInfo = nullptr;
	theVerdict = "PASS(Robust)";
	for( const auto & leafEC : theLeavesECVector )
	{
		securityAnalysisInfo = leafEC->getInformation()->getUniqSecurityAnalysisProcessorInfo();

AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
		AVM_OS_LOG << "For this leave EC: " << leafEC->str_min() << std::endl
					<< "The mark is: "
					<< securityAnalysisInfo->strTheAnalyzedMark()
					<< std::endl;
			AVM_OS_LOG << "Local K :" << std::endl
					<< securityAnalysisInfo->getLocalK()
					<< std::endl;
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

		if (securityAnalysisInfo->isMarked())
		{
			// we found a marked node for ONE path, is it robust or not?
			if (securityAnalysisInfo->getTheAnalyzedMark() == NOT_ROBUST)
			{
				theVerdict = "FAIL";
				break;
			}
		}
	}
*/
	// NEW: if we reach this point is because no FAIL was found, so we say PASS
AVM_IF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )
	AVM_OS_LOG << EMPHASIS(
			("THE EMITTED VERDICT IS : " + theVerdict), '=', 50);
AVM_ENDIF_DEBUG_LEVEL_FLAG( MEDIUM , PROCESSOR )

	return true;
}


/**
 * Info Serialization
 */
void SecurityAnalysisProcessorInfo::toStream(OutStream & os) const
{
	os << TAB << "TABLE{" << EOL;

	os << TAB << "}" << EOL_FLUSH;
}

void SecurityAnalysisProcessorInfo::toFscn(OutStream & os) const
{
	os << TAB << "TABLE{" << EOL;
	os << TAB << "}" << EOL_FLUSH;
}


} /* namespace sep */

