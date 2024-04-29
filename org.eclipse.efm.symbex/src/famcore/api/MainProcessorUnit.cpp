/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/
#include "MainProcessorUnit.h"

#include <fstream>

#include <computer/primitive/AvmCommunicationRdvPrimitive.h>

#include  <famcore/queue/ExecutionQueue.h>

#include <fml/builtin/Identifier.h>

#include <fml/runtime/ExecutionContext.h>
#include <fml/runtime/ExecutionData.h>
#include <fml/runtime/ExecutionInformation.h>
#include <fml/runtime/RuntimeDef.h>

#include <fml/trace/TraceFactory.h>

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include <sew/Configuration.h>
#include <sew/SymbexDispatcher.h>
#include <sew/SymbexControllerRequestManager.h>
#include <sew/WorkflowParameter.h>

#include <solver/api/SolverFactory.h>

#include <util/avm_vfs.h>

#include <boost/format.hpp>


namespace sep
{

/**
 * CONSTRUCTOR
 * Default
 */
MainProcessorUnit::MainProcessorUnit(
	SymbexControllerUnitManager & aManager, const WObject * wfParameterObject)
: RegisteredProcessorUnit(aManager,
		wfParameterObject, PRECEDENCE_OF_MAIN_PROCESSOR),
IDebugProcessorProvider( this ),

mNodeCountLimit ( AVM_NUMERIC_MAX_SIZE_T ),

mSymbexEvalCountLimit( AVM_NUMERIC_MAX_SIZE_T ),
mSymbexStepCountLimit( AVM_NUMERIC_MAX_SIZE_T ),

mNodeHeightLimit( AVM_NUMERIC_MAX_SIZE_T ),
mNodeWidthLimit ( AVM_NUMERIC_MAX_SIZE_T ),

mReportFrequency( AVM_NUMERIC_MAX_SIZE_T ),
mReportPoint( AVM_NUMERIC_MAX_SIZE_T ),

mSaveFrequency( AVM_NUMERIC_MAX_SIZE_T ),
mSavePoint( AVM_NUMERIC_MAX_SIZE_T ),

mStopCount( 0 ),

mDeadlockCount( 0 ),
mLivelockCount( 0 ),

mStatementExitCount( 0 ),

mStatementFatalErrorCount( 0 ),
mSymbolicExecutionLimitationCount( 0 ),

mMaxReachHeight( 1 ),
mMaxReachWidth( 1 ),

mInconditionalStopMarkerLocation(),
mInconditionalStopMarkerCheckingPeriod(AVM_NUMERIC_MAX_SIZE_T),

mInconditionalStopMarkerFlag( false ),

// Execution extension trace filter
mLocalExecutableForm( getConfiguration().getExecutableSystem() , 0 ),
mTraceObjective( OperatorManager::OPERATOR_OR ),
mTraceChecker( ENV, &mLocalExecutableForm ),

// INFO ID
mExitInfoID( new Identifier("@EXIT") ),
mExitAllInfoID( new Identifier("@EXIT_ALL") ),
mReturnInfoID( new Identifier("@RETURN") ),

////////////////////////////////////////////////////////////////////////////
// for local used
ptrEC( nullptr ),
mAnteWaitingQueue( )
{
	//!! NOTHING
}


/**
 ***************************************************************************
prototype filter::stop_criteria as avm::processor.MAIN is
	section PROPERTY
		@node   = 50;

		@report = 500000;
		@save   = 500000;

		@eval   = 100000;

		@height = 1000;
		@width  = 100;

		@loop#detection#trivial = true;
	endsection PROPERTY

	section LOG
		// %1% --> eval step count
		// %2% --> context count
		// %3% --> context height
		// %3% --> context width
		@eval   = "step:%1% , context:%2% , height:%3% , width:%4% ";
		@result = "step:%1% , context:%2% , height:%3% , width:%4% ";
		@report = "stop:%1% , context:%2% , height:%3% , width:%4% ";
	endsection LOG
endprototype
 ***************************************************************************
 */



/**
 * CONFIGURE
 */
bool MainProcessorUnit::configureImpl()
{
	AVM_OS_ASSERT_FATAL_ERROR_EXIT( hasParameterWObject() )
			<< "Unexpected a <null> MainProcessorUnit WObject !!!"
			<< SEND_EXIT;

	// Shell config
	const WObject * configSHELL = Query::getRegexWSequence(
			getParameterWObject(), WorkflowParameter::SECTION_SHELL_REGEX_ID);

	mInconditionalStopMarkerLocation =
			Query::getWPropertyString(configSHELL, "stop", "");
	if( mInconditionalStopMarkerLocation.empty() )
	{
		mInconditionalStopMarkerLocation =
				getConfiguration().getInconditionalStopMarkerLocation();
	}
	else
	{
		mInconditionalStopMarkerLocation =
				VFS::native_path(mInconditionalStopMarkerLocation);

		mInconditionalStopMarkerLocation = VFS::native_path(
				mInconditionalStopMarkerLocation, VFS::WorkspaceLogPath);
	}

	mInconditionalStopMarkerCheckingPeriod = 1000;
	mInconditionalStopMarkerFlag = false;


AVM_IF_DEBUG_ENABLED
	mConfigFlag = IDebugProcessorProvider::debugConfigureImpl(
			getParameterWObject() ) || mConfigFlag;
AVM_ENDIF_DEBUG_ENABLED


	if( not hasParameterWObject() )
	{
		return( mConfigFlag );
	}


	const WObject * thePROPERTY = Query::getWSequenceOrElse(
			getParameterWObject(), "limit", "PROPERTY");
	if( thePROPERTY != WObject::_NULL_ )
	{
		mNodeCountLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, SUFFIX_WID(OR_WID2("context", "node"), "count"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mReportPoint = mReportFrequency =
				Query::getRegexWPropertySizeT(thePROPERTY,
						PREFIX_WID("print", SUFFIX_WID("report", "frequency")),
						AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mInconditionalStopMarkerCheckingPeriod =
				Query::getRegexWPropertySizeT(thePROPERTY,
						SUFFIX_WID("stop", SUFFIX_WID("checking" , "frequency")),
						mInconditionalStopMarkerCheckingPeriod,
						mInconditionalStopMarkerCheckingPeriod);

		mSavePoint = mSaveFrequency =
				Query::getRegexWPropertySizeT(thePROPERTY,
						PREFIX_WID("serializer", SUFFIX_WID("save", "frequency")),
						AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mSymbexEvalCountLimit = Query::getRegexWPropertySizeT(thePROPERTY,
				OR_WID2(SUFFIX_WID("symbex", "eval"), "eval"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mSymbexStepCountLimit = Query::getRegexWPropertySizeT(thePROPERTY,
				PREFIX_WID("symbex", "step"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mNodeHeightLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, PREFIX_WID(OR_WID2("context", "node"), "height"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mNodeWidthLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, PREFIX_WID(OR_WID2("context", "node"), "width"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);
	}


	const WObject * theEXTENDER = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("extender", "EXTENDER"));
	if( (theEXTENDER != WObject::_NULL_) && theEXTENDER->hasOwnedElement() )
	{
		// Configuration of TRACE
		TraceFactory traceFactory(getConfiguration(), ENV,
				getParameterWObject(), mLocalExecutableForm);

		if( not traceFactory.configure(theEXTENDER, & mTraceObjective) )
		{
			return( false );
		}
	}

	return( mConfigFlag );
}


////////////////////////////////////////////////////////////////////////////////
// PROCESSING API
////////////////////////////////////////////////////////////////////////////////
/**
 * POST PROCESS
 */
bool MainProcessorUnit::collectExtendedContext()
{
	ListOfExecutionContext potentialInputEC;
	potentialInputEC.splice( getConfiguration().getInputContext() );

	for( const auto & itInputEC : potentialInputEC )
	{
		collectContext(getConfiguration().getInputContext(), *itInputEC);
	}

	return( true );
}


void MainProcessorUnit::collectContext(
		ListOfExecutionContext & inputContext, ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
		for( const auto & itEC : anEC )
		{
			collectContext(inputContext, *itEC);
		}
	}
	// case of leaf EC
	else if( anEC.hasFlags() || anEC.hasInfo() )
	{
		if( MainProcessorUnit::cleanFlagsIfReexecutable(anEC) )
		{
			appendIfRequiredExtension(inputContext, anEC);
		}
	}
	else
	{
		appendIfRequiredExtension(inputContext, anEC);
	}
}


void MainProcessorUnit::appendIfRequiredExtension(
		ListOfExecutionContext & inputContext, ExecutionContext & anEC)
{
	if( mTraceObjective.hasOperand()
		&& mTraceChecker.isSat(anEC, mTraceObjective) )
	{
		anEC.getwFlags().addCoverageElementTrace();

// TODO Create Info using the AvmCode of the mTraceObjective
		anEC.addInfo(*this,
				mTraceObjective.hasOneOperand()
						? mTraceObjective.first()
						: mTraceObjective.first() );

		anEC.getwFlags().setObjectiveAchievedTrace();
	}
	else
	{
		inputContext.append(& anEC);
	}
}


////////////////////////////////////////////////////////////////////////////////
// FILTERING API
////////////////////////////////////////////////////////////////////////////////

/**
 * preEval Filter
 */
bool MainProcessorUnit::prefilter()
{
	ecQueue = &( getExecutionQueue().getReadyQueue() );
	ecQueueItEnd = ecQueue->end();
	for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
	{
		if( not prefilter(* (*ecQueueIt)) )
		{
			getExecutionQueue().appendFailed( *ecQueueIt );

			ecQueueIt = ecQueue->erase(ecQueueIt);
		}
		else
		{
			++ecQueueIt;
		}
	}

	return( getExecutionQueue().hasReady() );
}


bool MainProcessorUnit::prefilter(ExecutionContext & anEC)
{
	std::uint32_t theSymbexStepCount = getSymbexDispatcher().getSymbexStepCount();
	std::uint32_t theNextEvalNumber  = getSymbexDispatcher().getEvalNumber();

	if( (not mInconditionalStopMarkerFlag)
		&& (not mInconditionalStopMarkerLocation.empty())
		&& ((theNextEvalNumber % mInconditionalStopMarkerCheckingPeriod) == 0) )
	{
		checkReadEvalStopScript();
	}

	if( mInconditionalStopMarkerFlag )
	{
		anEC.getwFlags().setInterruptUserRequest();

		return( false );
	}


	if( (mSymbexEvalCountLimit    > theNextEvalNumber )
		&& (mSymbexStepCountLimit > theSymbexStepCount)

//		&& (mNodeCountLimit  >= anEC.getIdNumber())
		&& (mNodeCountLimit  >= ExecutionContextHeader::ID_NUMBER)

		&& (mNodeHeightLimit >= anEC.getHeight())
		&& (mNodeWidthLimit  >= anEC.getWidth()) )
	{
		if( theSymbexStepCount > mReportPoint )
		{
			AVM_OS_INFO << EOL << EMPHASIS("Report Point ...", '*', 80);
			getControllerUnitManager().report( AVM_OS_TRACE );
			getControllerUnitManager().report( AVM_OS_COUT  );
			getControllerUnitManager().report( AVM_OS_LOG   );

			mReportPoint = mReportPoint + mReportFrequency;
		}

		if( theSymbexStepCount > mSavePoint )
		{
			AVM_OS_WARN  << EMPHASIS("Save Point ...", '*', 80);

			getConfiguration().serializeComputingResult();

			mSavePoint = mSavePoint + mSaveFrequency;
		}
		return( true );
	}
	else
	{
		++mStopCount;

		if( mSymbexEvalCountLimit <= theNextEvalNumber )
		{
			anEC.getwFlags().addReachedSymbexEvalLimit();
		}

		if( mSymbexStepCountLimit <= theSymbexStepCount )
		{
			anEC.getwFlags().addReachedSymbexStepLimit();
		}

//		if( mNodeCountLimit < anEC.getIdNumber() )
		if( mNodeCountLimit < ExecutionContextHeader::ID_NUMBER )
		{
			anEC.getwFlags().addReachedNodeCountLimit();
		}

		if( mNodeHeightLimit < anEC.getHeight() )
		{
			anEC.getwFlags().addReachedNodeHeightLimit();
		}
		if( mNodeWidthLimit < anEC.getWidth() )
		{
			anEC.getwFlags().addReachedNodeWidthLimit();
		}

		return( false );
	}
}


bool MainProcessorUnit::finalizePrefiltering()
{
//	ecQueue = &( getExecutionQueue().getReadyQueue() );
//	ecQueueItEnd = ecQueue->end();
//	for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
//	{
//		setContextWidth( *ecQueueIt );
//
//		if( (*ecQueueIt)->getWidth() > mNodeWidthLimit )
//		{
//			(*ecQueueIt)->getwFlags().addReachedNodeWidthLimit();
//			(*ecQueueIt)->addInfo(*this, INFO_STOP_WIDTH_DATA);
//
//			getExecutionQueue().appendFailed( *ecQueueIt );
//
//			ecQueueIt = ecQueue->erase(ecQueueIt);
//		}
//		else
//		{
//			++ecQueueIt;
//		}
//	}
//
//	return( getExecutionQueue().hasReady() );

	return( true );
}


/**
 * postFilter
 * Every post filter has to implement this method
 */
bool MainProcessorUnit::postfilter()
{
	ecQueue = &( getExecutionQueue().getResultQueue() );
	ecQueueItEnd = ecQueue->end();
	for( ecQueueIt = ecQueue->begin() ; ecQueueIt != ecQueueItEnd ; )
	{
		if( postfilter(* (*ecQueueIt)) )
		{
			ptrEC = (*ecQueueIt);
			++ecQueueIt;

			switch( ptrEC->getExecutionData().getAEES() )
			{
				case AEES_OK:
				case AEES_STMNT_NOTHING:
				case AEES_STEP_MARK:
				{
					break;
				}

				case AEES_STMNT_FINAL:
				{
					ExecutionData & apED = ptrEC->getwExecutionData();
					if( not apED.isFinalized(apED.getSystemRID()) )
					{
						apED.mwsetAEES( AEES_OK );
					}
					break;
				}

				case AEES_STMNT_DESTROY:
				{
					ExecutionData & apED = ptrEC->getwExecutionData();
					if( not apED.isDestroyed(apED.getSystemRID()) )
					{
						apED.mwsetAEES( AEES_OK );
					}
					break;
				}

				case AEES_STMNT_RETURN:
				case AEES_STMNT_EXIT:
				{
					break;
				}

				case AEES_STMNT_EXIT_ALL:
				{
					mInconditionalStopMarkerFlag = true;

					ptrEC->getwFlags().setInterruptUserRequest();

					break;
				}

				case AEES_STMNT_FATAL_ERROR:
				{
					mInconditionalStopMarkerFlag = true;

					ptrEC->getwFlags().setExecutionFatalErrorTrace();

					break;
				}

				case AEES_SYMBOLIC_EXECUTION_LIMITATION:
				{
					ptrEC->getwFlags().setExecutionSymbexLimitationTrace();

					break;
				}

				case AEES_WAITING_INCOM_RDV:
				case AEES_WAITING_OUTCOM_RDV:
				{
					// TODO !!! PAS NORMAL !!!
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected << WAITING_??COM_RDV >> "
								"ENDIND EXECUTION STATUS !!!"
							<< SEND_EXIT;

					break;
				}

				case AEES_WAITING_JOIN_FORK:
				{
					break;
				}

				case AEES_STMNT_BREAK:
				case AEES_STMNT_CONTINUE:
				{
					// TODO !!! PAS NORMAL !!!
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES(
									ptrEC->getExecutionData().getAEES())
							<< " !!!"
							<< SEND_EXIT;

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES(
									ptrEC->getExecutionData().getAEES())
							<< " !!!"
							<< SEND_EXIT;

					break;
				}
			}
		}
		else
		{
			getExecutionQueue().appendFailed( *ecQueueIt );

			ecQueueIt = ecQueue->erase(ecQueueIt);
		}
	}

	return( getExecutionQueue().hasResult() );
}


bool MainProcessorUnit::postfilter(ExecutionContext & anEC)
{
//	if( SolverFactory::solveParameters(anEC.getExecutionData()) )
//	{
//		AVM_OS_TRACE << "SolverFactory::solveParameters for "
//				<< anEC.str_min() << std::endl << "Condition :> "
//				<< anEC.getExecutionData()->getAllPathCondition().str()
//				<< std::endl;
//		anEC.getExecutionData()->getParametersRuntimeForm()->toStreamData(
//				anEC.getExecutionData(), AVM_OS_TRACE, "\t");
//	}

	// STAT for an EFFECTIVE EVAL CONTEXT
	if( anEC.getHeight() > mMaxReachHeight )
	{
		mMaxReachHeight = anEC.getHeight();
	}
	if( anEC.getWidth() > mMaxReachWidth )
	{
		mMaxReachWidth = anEC.getWidth();
	}

//	// STAT for an EFFECTIVE CONSTRUCT CONTEXT
//	ecEnd = anEC.end();
//	for( ecIt = anEC.begin() ; ecIt != ecEnd ; ++ecIt )
//	{
//		if( (*ecIt)->getHeight() > mMaxReachHeight )
//		{
//			mMaxReachHeight = (*ecIt)->getHeight();
//		}
//		if( (*ecIt)->getWidth() > mMaxReachWidth )
//		{
//			mMaxReachWidth = (*ecIt)->getWidth();
//		}
//	}

	return( true );
}

bool MainProcessorUnit::finalizePostfiltering()
{
	if( getExecutionQueue().getAnteWaitingQueue().empty() )
	{
		ecQueue = &( getExecutionQueue().getResultQueue() );

		while( ecQueue->nonempty() )
		{
			ecQueue->pop_first_to( ptrEC );

			if( ptrEC->hasChildContext()  )
			{
				ecChildIt = ptrEC->begin();
				ecChildItEnd = ptrEC->end();
				for( ; ecChildIt != ecChildItEnd ; ++ecChildIt )
				{
					finalizePostfiltering( * (*ecChildIt) );
				}

				if( _AVM_EXEC_MODE_ != AVM_EXEC_SERVER_GRPC_MODE )
				{
					if( ptrEC->singleChildContext()
						&& ptrEC->edTEQ( *(ptrEC->firstChildContext()) ) )
					{
						++mLivelockCount;

						ptrEC->getwFlags().setExecutionLivelockTrace();
					}
				}
			}
			else // No Child !
			{
				++mDeadlockCount;

				ptrEC->getwFlags().setExecutionDeadlockTrace();
			}
		}

	}
	else
	{
		ecQueue = &( getExecutionQueue().getAnteWaitingQueue() );

		while( ecQueue->nonempty() )
		{
			ecQueue->pop_first_to( ptrEC );

			finalizePostfiltering( *ptrEC );
		}
	}

	getExecutionQueue().smartPushWaiting( mAnteWaitingQueue );

	mAnteWaitingQueue.clear();

	getExecutionQueue().getResultQueue().clear();

	return( true );
}


bool MainProcessorUnit::finalizePostfiltering(ExecutionContext & aChildEC)
{
	switch( aChildEC.getExecutionData().getAEES() )
	{
		case AEES_OK:
		case AEES_WAITING_JOIN_FORK:
		{
			setContextWidth( aChildEC );

			mAnteWaitingQueue.append( &aChildEC );

			break;
		}

		case AEES_STEP_MARK:
		{
			aChildEC.getwFlags().setExecutionStepMarkTrace();

			setContextWidth( aChildEC );

			mAnteWaitingQueue.append( &aChildEC );

			break;
		}

		case AEES_STMNT_NOTHING:
		{
			aChildEC.getPrevious()->removeChildContext(& aChildEC );

//			if( (& aChildEC) == ptrEC->begin() )
//			{
//				/*ecChildIt =*/ ptrEC->eraseChildContext( ecChildIt );
//			}
//			else
//			{
//				ecChildIt = ptrEC->eraseChildContext( ecChildIt );
//
//				--ecChildIt;
//			}

			break;
		}

		case AEES_STMNT_RETURN:
		{
			++mStatementExitCount;

			setContextWidth( aChildEC );

			aChildEC.getwFlags().setExecutionStatementExitTrace();

			if( aChildEC.getExecutionData().hasValue() )
			{
				aChildEC.addInfo(*this, mReturnInfoID,
						aChildEC.getExecutionData().getValue() );
			}

			break;
		}

		case AEES_STMNT_EXIT:
		{
			++mStatementExitCount;

			setContextWidth( aChildEC );

			aChildEC.getwFlags().setExecutionStatementExitTrace();

			if( aChildEC.getExecutionData().hasValue() )
			{
				aChildEC.addInfo(*this, mExitInfoID,
						aChildEC.getExecutionData().getValue() );
			}

			break;
		}

		case AEES_STMNT_EXIT_ALL:
		{
			++mStatementExitCount;
			mInconditionalStopMarkerFlag = true;

			setContextWidth( aChildEC );

			aChildEC.getwFlags().setInterruptUserRequest();

			aChildEC.addInfo(*this, mExitAllInfoID, mExitAllInfoID);

			break;
		}

		case AEES_STMNT_FATAL_ERROR:
		{
			++mStatementFatalErrorCount;

			aChildEC.getwFlags().setExecutionFatalErrorTrace();

			break;
		}

		case AEES_SYMBOLIC_EXECUTION_LIMITATION:
		{
			++mSymbolicExecutionLimitationCount;

			aChildEC.getwFlags().setExecutionSymbexLimitationTrace();

			break;
		}


		case AEES_WAITING_INCOM_RDV:
		case AEES_WAITING_OUTCOM_RDV:

		case AEES_STMNT_FINAL:
		case AEES_STMNT_DESTROY:

		case AEES_STMNT_BREAK:
		case AEES_STMNT_CONTINUE:
		{
			// TODO !!! PAS NORMAL !!!
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected ENDIND EXECUTION STATUS :> "
					<< RuntimeDef::strAEES(
							(*ecChildIt)->getExecutionData().getAEES() )
					<< " !!!"
					<< SEND_EXIT;

			return( false );
		}

		default:
		{
			AVM_OS_FATAL_ERROR_EXIT
					<< "Unexpected ENDIND EXECUTION STATUS << "
					<< RuntimeDef::strAEES(
							(*ecChildIt)->getExecutionData().getAEES() )
					<< " >> !!!"
					<< SEND_EXIT;

			return( false );
		}
	}

	return( true );
}



void MainProcessorUnit::setContextWidth(ExecutionContext & anEC)
{
	// STAT after EVAL for WIDTH
	if( anEC.hasContainer() && anEC.getContainer()->hasChildContext() )
	{
		if( (anEC.getContainer()->firstChildContext() == (& anEC)) )
		{
			anEC.setWidth( anEC.getContainer()->getWidth() );
		}
		else
		{
			anEC.setWidth( getSymbexDispatcher().nextGlobalGraphWidth() );
		}
	}
}



/**
 * MAIN PROCESSOR
 * REPORT
 */
void MainProcessorUnit::reportSilent(OutStream & out) const
{
	const std::string & dbgSuffix =
			(isDebugEnabled() ? "< debug = true > " : " ");
	reportHeader(out, "SUPERVISOR" + dbgSuffix);

	if( mDeadlockCount > 0 )
	{
		out << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		out << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}

	if( mStatementExitCount > 0 )
	{
		out << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		out << TAB2 << "The FATAL#ERROR count : "
			<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		out << TAB2 << "The SYMB#LIMIT count  : "
			<< mSymbolicExecutionLimitationCount << EOL;
	}

	out << std::flush;
}


void MainProcessorUnit::reportMinimum(OutStream & out) const
{
	const std::string & dbgSuffix =
			(isDebugEnabled() ? "< debug = true > " : " ");
	reportHeader(out, "SUPERVISOR" + dbgSuffix);

	out << TAB2 << "The CONTEXT  count : "
		<< ExecutionContextHeader::ID_NUMBER << EOL;

	if( getSymbexDispatcher().getSymbexStepCount()
			!= getSymbexDispatcher().getEvalNumber() )
	{
		out << TAB2 << "The RUN EVAL count : "
			<< getSymbexDispatcher().getEvalNumber() << EOL;
	}
	out << TAB2 << "The RUN STEP count : "
		<< getSymbexDispatcher().getSymbexStepCount() << EOL << EOL

		<< TAB2 << "The Max HEIGHT reaching : " << mMaxReachHeight << EOL

		<< TAB2 << "The Max WIDTH  reaching : " << mMaxReachWidth  << EOL;

	if( mDeadlockCount > 0 )
	{
		out << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		out << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}

	if( mStatementExitCount > 0 )
	{
		out << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		out << TAB2 << "The FATAL#ERROR count : "
				<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		out << TAB2 << "The SYMB#LIMIT count  : "
				<< mSymbolicExecutionLimitationCount << EOL;
	}

	AvmCommunicationRdvPrimitive::reportGlobalStatistics( out );

	out << std::flush;
}


void MainProcessorUnit::reportDefault(OutStream & out) const
{
	const std::string & dbgSuffix =
			(isDebugEnabled() ? "< debug = true > " : " ");
	reportHeader(out, "SUPERVISOR" + dbgSuffix);

	out << TAB2 << "The CONTEXT  count : "
		<< ExecutionContextHeader::ID_NUMBER << EOL << EOL;

	if( getSymbexDispatcher().getSymbexStepCount()
			!= getSymbexDispatcher().getEvalNumber() )
	{
		out << TAB2 << "The RUN EVAL count : "
			<< getSymbexDispatcher().getEvalNumber() << EOL;
	}
	out << TAB2 << "The RUN STEP count : "
		<< getSymbexDispatcher().getSymbexStepCount() << EOL

		<< TAB2 << "The GLOBAL  STOP count  : " << mStopCount << EOL << EOL

		<< TAB2 << "The Max HEIGHT reaching : " << mMaxReachHeight << EOL

		<< TAB2 << "The Max WIDTH  reaching : " << mMaxReachWidth  << EOL;

	if( mDeadlockCount > 0 )
	{
		out << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		out << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}
	if( mStatementExitCount > 0 )
	{
		out << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		out << TAB2 << "The FATAL#ERROR count : "
			<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		out << TAB2 << "The SYMB#LIMIT count  : "
			<< mSymbolicExecutionLimitationCount << EOL;
	}

	AvmCommunicationRdvPrimitive::reportGlobalStatistics( out );

	out << std::flush;
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void MainProcessorUnit::tddRegressionReportImpl(OutStream & out) const
{
//	os << TAB << "CONTEXT  count : "
//			<< ExecutionContextHeader::ID_NUMBER << EOL;

	if( getSymbexDispatcher().getSymbexStepCount()
			!= getSymbexDispatcher().getEvalNumber() )
	{
		out << TAB2 << "The RUN EVAL count : "
			<< getSymbexDispatcher().getEvalNumber() << EOL;
	}
	out << TAB << "RUN STEP count : "
		<< getSymbexDispatcher().getSymbexStepCount()
		<< EOL_FLUSH;
}


/**
 * EVAL TRACE
 */

static int EVAL_STEP_CURRENT_WIDTH   = 3;
static int NODE_COUNT_CURRENT_WIDTH  = 3;

static int NODE_HEIGHT_CURRENT_WIDTH = 3;
static int NODE_WIDTH_CURRENT_WIDTH  = 3;


inline static std::size_t POW10( int n )
{
	switch( n )
	{
		case 3 : return( 1000     );
		case 4 : return( 10000    );
		case 5 : return( 100000   );
		case 6 : return( 1000000  );
		case 7 : return( 10000000 );
		default: return( static_cast<std::size_t>( std::pow(10, n) ) );
	}
}


inline static std::string traceBound(std::size_t limit, int width)
{
	std::ostringstream oss;
	if( limit < AVM_NUMERIC_MAX_SIZE_T )
	{
		( (limit < POW10(width))? oss << std::setw(width) : oss ) << limit;
	}
	else
	{
		oss << "00";//"oxo";
	}

	return( oss.str() );
}

inline static std::string traceSpider(std::size_t limit)
{
	std::ostringstream oss;
	if( limit < AVM_NUMERIC_MAX_SIZE_T )
	{
		oss << limit;
	}
	else
	{
		oss << "00";//"oxo";
	}

	return( oss.str() );
}

void MainProcessorUnit::traceBoundEval(OutStream & os) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin() )
		{
			itProcessor->traceBoundEval(oss);
		}
	}

	boost::format formatter(mBoundEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << TAB << formatter
			% traceBound(mSymbexStepCountLimit , EVAL_STEP_CURRENT_WIDTH)
			% traceBound(mNodeCountLimit       , NODE_COUNT_CURRENT_WIDTH)
			% traceBound(mNodeHeightLimit      , NODE_HEIGHT_CURRENT_WIDTH)
			% traceBound(mNodeWidthLimit       , NODE_WIDTH_CURRENT_WIDTH)
			% oss.str()
			<< std::flush;
}


inline static std::string currentTrace(std::size_t count, int & width)
{
	std::ostringstream oss;

	oss << std::setw( ( count < POW10(width) )? width : ++width ) << count;

	return( oss.str() );
}


//!! Warning: Unused static function
//static std::string traceElement(std::size_t count, std::size_t limit, int width)
//{
//	std::ostringstream oss;
//	oss << std::setw( width ) << count;
//	if( limit < AVM_NUMERIC_MAX_SIZE_T )
//	{
//		oss << " / " << std::setw( width ) << limit;
//	}
//
//	return( oss.str() );
//}

// SPIDER TRACE POSITION
void MainProcessorUnit::traceInitSpider(OutStream & os) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin()
			&& itProcessor->isLifecycleRunnable() )
		{
			itProcessor->traceInitSpider(oss);
		}
	}

	boost::format formatter(mSpiderInitTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << TAB << formatter
			% traceSpider(mSymbexStepCountLimit)
			% traceSpider(mNodeCountLimit)
			% traceSpider(mNodeHeightLimit)
			% traceSpider(mNodeWidthLimit)
			% oss.str()
			<< std::flush;
}

void MainProcessorUnit::traceStepSpider(
		OutStream & os, const ExecutionContext & anEC) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin()
			&& itProcessor->isLifecycleRunnable() )
		{
			itProcessor->traceStepSpider(oss, anEC);
		}
	}

	boost::format formatter(mSpiderStepTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << TAB << formatter
			% anEC.getEvalNumber()
			% anEC.getIdNumber()
			% anEC.getHeight()
			% anEC.getWidth()
			% oss.str()
			<< std::flush;
}

void MainProcessorUnit::traceStopSpider(OutStream & os) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin()
			&& itProcessor->isLifecycleRunnable() )
		{
			itProcessor->traceStopSpider(oss);
		}
	}

	boost::format formatter(mSpiderStopTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

	os << TAB << formatter
			% getSymbexDispatcher().getEvalNumber()
			% ExecutionContext::getCreateCounter()
			% mMaxReachHeight
			% mMaxReachWidth
			% oss.str()
			<< std::flush;
}

// SYMBEX EVALUATION TRACE INFORMATION
void MainProcessorUnit::traceMinimumPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin()
			&& itProcessor->isLifecycleRunnable() )
		{
			itProcessor->traceMinimumPreEval(oss, anEC);
		}
	}

	boost::format formatter(mPreEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

//	os << TAB << formatter
//			% traceElement(anEC->getEvalNumber(), mEvalStepLimit  , 5)
//			% traceElement(anEC->getIdNumber()  , mNodeNodeLimit  , 6)
//			% traceElement(anEC->getHeight()    , mNodeHeightLimit, 5)
//			% traceElement(anEC->getWidth()     , mNodeWidthLimit , 5)

	os << TAB << formatter
			% currentTrace(anEC.getEvalNumber(), EVAL_STEP_CURRENT_WIDTH)
			% currentTrace(anEC.getIdNumber()  , NODE_COUNT_CURRENT_WIDTH)
			% currentTrace(anEC.getHeight()    , NODE_HEIGHT_CURRENT_WIDTH)
			% currentTrace(anEC.getWidth()     , NODE_WIDTH_CURRENT_WIDTH)
			% oss.str()
			<< std::flush;
}



void MainProcessorUnit::traceDefaultPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	os << TAB << DEFAULT_WRAP_DATA << "E[" << std::setw(4)
			<< anEC.getEvalNumber() << "] " << anEC.str_min()
			<< END_WRAP_EOL;
}


void MainProcessorUnit::traceMinimumPostEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	//!! NOTHING
}

void MainProcessorUnit::traceDefaultPostEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	anEC.traceDefaultPostEval( os << DEFAULT_WRAP_DATA );

	os << END_WRAP;
}


void MainProcessorUnit::reportEval(OutStream & os) const
{
	OSS oss;
	for( const auto & itProcessor :
			getControllerUnitManager().getControllerUnits() )
	{
		if( itProcessor->isEnablePlugin() )
		{
			itProcessor->reportEval(oss);
		}
	}

	boost::format formatter(mReportEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

//	os << TAB << formatter
//		% traceElement(getSymbexDispatcher().getEvalNumber(), mEvalStepLimit, 5)
//
//		% traceElement(ExecutionContext::getCreateCounter(), mNodeCountLimit, 6)
//
//		% traceElement(mMaxReachHeight , mHeightLimit, 6)
//		% traceElement(mMaxReachWidth  , mWidthLimit , 6)

	os << TAB << formatter
		% currentTrace( getSymbexDispatcher().getEvalNumber(),
				EVAL_STEP_CURRENT_WIDTH)

		% currentTrace(ExecutionContext::getCreateCounter(),
				NODE_COUNT_CURRENT_WIDTH)

		% currentTrace(mMaxReachHeight, NODE_HEIGHT_CURRENT_WIDTH)
		% currentTrace(mMaxReachWidth , NODE_WIDTH_CURRENT_WIDTH)
		% oss.str()
		<< std::flush;
}


////////////////////////////////////////////////////////////////////////////////
// DEBUG PROCESSING API
////////////////////////////////////////////////////////////////////////////////

bool MainProcessorUnit::debugEvalCommandImpl()
{
	return( false );
}


void MainProcessorUnit::checkReadEvalStopScript()
{
	std::ifstream anInconditionalStopMarkerStream(
			mInconditionalStopMarkerLocation.c_str() );

	if( anInconditionalStopMarkerStream.good() )
	{
		mInconditionalStopMarkerFlag = true;

		if( isDebugScript(anInconditionalStopMarkerStream) )
		{
			mInconditionalStopMarkerFlag = false;

			debugReadEvalScript(anInconditionalStopMarkerStream);
		}
	}

	anInconditionalStopMarkerStream.close();

	if( mInconditionalStopMarkerFlag )
	{
		AVM_OS_WARN << EMPHASIS("UNCONDITIONAL STOP !!!");

		++mStopCount;

		getSymbexRequestManager().postRequestStop( this );
	}
}


}
