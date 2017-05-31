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

#include <fam/api/ProcessorUnitRepository.h>

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
#include <sew/Workflow.h>

#include <solver/api/SolverFactory.h>

#include <util/avm_vfs.h>

#include <boost/format.hpp>


namespace sep
{


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
	WObject * configSHELL = Query::getRegexWSequence(
			getParameterWObject(), Workflow::SECTION_SHELL_REGEX_ID);

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


	WObject * thePROPERTY = Query::getWSequenceOrElse(
			getParameterWObject(), "limit", "PROPERTY");
	if( thePROPERTY != WObject::_NULL_ )
	{
		mNodeCountLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, SUFFIX_WID("node", "count"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mReportPoint = mReportFrequency =
				Query::getWPropertySizeT(thePROPERTY, "report",
						AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mSavePoint = mSaveFrequency =
				Query::getWPropertySizeT(thePROPERTY, "save",
						AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);
//		if( mSaveFrequency < 100 )
//		{
//AVM_IF_DEBUG_FLAG( CONFIGURING )
//	AVM_OS_LOG << "Invalid save period << " << mSaveFrequency
//			<< " >> => replace by << " << 10 * mSaveFrequency << " >> !!!"
//			<< std::endl;
//AVM_ENDIF_DEBUG_FLAG( CONFIGURING )
//
//			mSavePoint = mSaveFrequency = 10 * mSaveFrequency;
//		}

		mEvalStepLimit = Query::getRegexWPropertySizeT(thePROPERTY,
				OR_WID2(SUFFIX_WID("(run|eval)", "step"), "step"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mNodeHeightLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, PREFIX_WID("node", "height"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);

		mNodeWidthLimit = Query::getRegexWPropertySizeT(
				thePROPERTY, PREFIX_WID("node", "width"),
				AVM_NUMERIC_MAX_SIZE_T, AVM_NUMERIC_MAX_SIZE_T);
	}


	WObject * theEXTENDER = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("extender", "EXTENDER"));
	if( (theEXTENDER != WObject::_NULL_) && theEXTENDER->hasOwnedElement() )
	{
		// Configuration of TRACE
		TraceFactory traceFactory(getConfiguration(), ENV,
				getParameterWObject(), &mLocalExecutableForm);

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

	ListOfExecutionContext::const_iterator it = potentialInputEC.begin();
	ListOfExecutionContext::const_iterator itEnd = potentialInputEC.end();
	for( ; it != itEnd ; ++it )
	{
		collectContext(getConfiguration().getInputContext(), *(*it));
	}

	return( true );
}


void MainProcessorUnit::collectContext(
		ListOfExecutionContext & inputContext, ExecutionContext & anEC)
{
	if( anEC.hasChildContext() )
	{
		ExecutionContext::rw_child_iterator it = anEC.begin();
		ExecutionContext::rw_child_iterator itEnd = anEC.end();
		for( ; it != itEnd ; ++it )
		{
			collectContext(inputContext, *(*it));
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
	if( mTraceObjective.nonempty()
		&& mTraceChecker.isSat(anEC, mTraceObjective) )
	{
		anEC.getwFlags().addCoverageElementTrace();

// TODO Create Info using the AvmCode of the mTraceObjective
		anEC.addInfo(*this,
				mTraceObjective.singleton()
						? mTraceObjective.first()
						: mTraceObjective.first() );

		anEC.getwFlags().addObjectiveAchievedTrace();
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
	avm_uint32_t theNextEvalNumber = getSymbexDispatcher().getEvalNumber();

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


	if( (mEvalStepLimit   >  theNextEvalNumber)

//		&& (mNodeCountLimit  >= anEC.getIdNumber())
		&& (mNodeCountLimit  >= ExecutionContextHeader::ID_NUMBER)

		&& (mNodeHeightLimit >= anEC.getHeight())
		&& (mNodeWidthLimit  >= anEC.getWidth()) )
	{
		if( theNextEvalNumber > mReportPoint )
		{
			AVM_OS_INFO << EOL << EMPHASIS("Report Point ...", '*', 80);
			getControllerUnitManager().report( AVM_OS_TRACE );
			getControllerUnitManager().report( AVM_OS_COUT  );
			getControllerUnitManager().report( AVM_OS_LOG   );

			mReportPoint = mReportPoint + mReportFrequency;
		}

		if( theNextEvalNumber > mSavePoint )
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

		if( mEvalStepLimit <= theNextEvalNumber )
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

			switch( ptrEC->refExecutionData().getAEES() )
			{
				case AEES_OK:
				case AEES_STMNT_NOTHING:
				case AEES_STEP_MARK:
				{
					break;
				}

				case AEES_STMNT_FINAL:
				{
					APExecutionData & apED = ptrEC->getAPExecutionData();
					if( not apED->isFinalized(apED->getSystemRID()) )
					{
						apED.mwsetAEES( AEES_OK );
					}
					break;
				}

				case AEES_STMNT_DESTROY:
				{
					APExecutionData & apED = ptrEC->getAPExecutionData();
					if( not apED->isDestroyed(apED->getSystemRID()) )
					{
						apED.mwsetAEES( AEES_OK );
					}
					break;
				}

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
				case AEES_STMNT_RETURN:
				{
					// TODO !!! PAS NORMAL !!!
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES(
									ptrEC->getExecutionData()->mAEES) << " !!!"
							<< SEND_EXIT;

					break;
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES(
									ptrEC->getExecutionData()->mAEES) << " !!!"
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
//	if( SolverFactory::solveParameters(anEC.getAPExecutionData()) )
//	{
//		AVM_OS_TRACE << "SolverFactory::solveParameters for "
//				<< anEC.str_min() << std::endl << "Condition :> "
//				<< anEC.getAPExecutionData()->getAllPathCondition().str()
//				<< std::endl;
//		anEC.getAPExecutionData()->getParametersRuntimeForm()->toStreamData(
//				anEC.getAPExecutionData(), AVM_OS_TRACE, "\t");
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

	// STAT for an EFFECTIVE CONSTRUCT CONTEXT
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

	if( anEC.noChildContext() )
	{
		++mDeadlockCount;

		anEC.getwFlags().setExecutionDeadlockTrace();
	}
	else if( anEC.singleChildContext()
			&& (anEC.getExecutionData()
				== anEC.firstChildContext()->getExecutionData()) )
	{
		++mLivelockCount;

		anEC.getwFlags().setExecutionLivelockTrace();
	}
	else
	{
		ecChildItEnd = anEC.end();
		for( ecChildIt = anEC.begin() ; ecChildIt != ecChildItEnd ; ++ecChildIt )
		{
			ptrEC = (*ecChildIt);

			switch( ptrEC->refExecutionData().getAEES() )
			{
				case AEES_STEP_MARK:
				{
					ptrEC->getwFlags().setExecutionStepMarkTrace();
					break;
				}

				default:
				{
					break;
				}
			}
		}
	}

	return( true );
}


bool MainProcessorUnit::finalizePostfiltering()
{
	childEC.clear();

	ecQueue = &( getExecutionQueue().getResultQueue() );
	while( ecQueue->nonempty() )
	{
		ecQueue->pop_first_to( ptrEC );

		ecChildIt = ptrEC->begin();
		ecChildItEnd = ptrEC->end();
		for( ; ecChildIt != ecChildItEnd ; ++ecChildIt )
		{
			switch( (*ecChildIt)->refExecutionData().getAEES() )
			{
				case AEES_OK:
				case AEES_STEP_MARK:
				case AEES_WAITING_JOIN_FORK:
				{
					setContextWidth( *ecChildIt );

					childEC.append( *ecChildIt );

					break;
				}

				case AEES_STMNT_NOTHING:
				{
					if( ecChildIt == ptrEC->begin() )
					{
						/*ecChildIt =*/ ptrEC->eraseChildContext( ecChildIt );
					}
					else
					{
						ecChildIt = ptrEC->eraseChildContext( ecChildIt );

						--ecChildIt;
					}

					break;
				}

				case AEES_STMNT_EXIT:
				{
					++mStatementExitCount;

					setContextWidth( *ecChildIt );

					(*ecChildIt)->getwFlags().setExecutionStatementExitTrace();

					break;
				}

				case AEES_STMNT_EXIT_ALL:
				{
					++mStatementExitCount;
					mInconditionalStopMarkerFlag = true;

					setContextWidth( *ecChildIt );

					ptrEC->getwFlags().setInterruptUserRequest();

					break;
				}

				case AEES_STMNT_FATAL_ERROR:
				{
					++mStatementFatalErrorCount;

					ptrEC->getwFlags().setExecutionFatalErrorTrace();

					break;
				}

				case AEES_SYMBOLIC_EXECUTION_LIMITATION:
				{
					++mSymbolicExecutionLimitationCount;

					ptrEC->getwFlags().setExecutionSymbexLimitationTrace();

					break;
				}


				case AEES_WAITING_INCOM_RDV:
				case AEES_WAITING_OUTCOM_RDV:

				case AEES_STMNT_FINAL:
				case AEES_STMNT_DESTROY:

				case AEES_STMNT_BREAK:
				case AEES_STMNT_CONTINUE:
				case AEES_STMNT_RETURN:
				{
					// TODO !!! PAS NORMAL !!!
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS :> "
							<< RuntimeDef::strAEES( (*ecChildIt)->
									getExecutionData()->mAEES ) << " !!!"
							<< SEND_EXIT;

					return( false );
				}

				default:
				{
					AVM_OS_FATAL_ERROR_EXIT
							<< "Unexpected ENDIND EXECUTION STATUS << "
							<< RuntimeDef::strAEES(	(*ecChildIt)->
									getExecutionData()->mAEES ) << " >> !!!"
							<< SEND_EXIT;

					return( false );
				}
			}
		}

		getExecutionQueue().pushWaitingChild( childEC );

		childEC.clear();
	}

	return( true );
}



void MainProcessorUnit::setContextWidth(ExecutionContext * anEC)
{
	// STAT after EVAL for WIDTH
	if( anEC->hasContainer() && anEC->getContainer()->hasChildContext() )
	{
		if( (anEC->getContainer()->firstChildContext() == anEC) )
		{
			anEC->setWidth( anEC->getContainer()->getWidth() );
		}
		else
		{
			anEC->setWidth( getSymbexDispatcher().nextGlobalGraphWidth() );
		}
	}
}



/**
 * MAIN PROCESSOR
 * REPORT
 */
void MainProcessorUnit::reportSilent(OutStream & os) const
{
	if( mDeadlockCount > 0 )
	{
		os << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		os << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}

	if( mStatementExitCount > 0 )
	{
		os << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		os << TAB2 << "The FATAL#ERROR count : "
				<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		os << TAB2 << "The SYMB#LIMIT count  : "
				<< mSymbolicExecutionLimitationCount << EOL;
	}

	os << std::flush;
}

void MainProcessorUnit::reportMinimum(OutStream & os) const
{
	reportHeader(os, "STOP CRITERIA ");

	os << TAB2 << "The CONTEXT  count : "
			<< ExecutionContextHeader::ID_NUMBER << EOL;

	os << TAB2 << "The RUN STEP count : "
			<< getSymbexDispatcher().getEvalNumber() << EOL << EOL;

	os << TAB2 << "The Max HEIGHT reaching : " << mMaxReachHeight << EOL;

	os << TAB2 << "The Max WIDTH  reaching : " << mMaxReachWidth  << EOL;

	if( mDeadlockCount > 0 )
	{
		os << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		os << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}

	if( mStatementExitCount > 0 )
	{
		os << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		os << TAB2 << "The FATAL#ERROR count : "
				<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		os << TAB2 << "The SYMB#LIMIT count  : "
				<< mSymbolicExecutionLimitationCount << EOL;
	}

	os << std::flush;
}


void MainProcessorUnit::reportDefault(OutStream & os) const
{
	reportHeader(os, "STOP CRITERIA ");

	os << TAB2 << "The CONTEXT  count : "
			<< ExecutionContextHeader::ID_NUMBER << EOL << EOL;

	os << TAB2 << "The RUN STEP count : "
			<< getSymbexDispatcher().getEvalNumber() << EOL;

	os << TAB2 << "The GLOBAL  STOP count  : " << mStopCount << EOL << EOL;

	os << TAB2 << "The Max HEIGHT reaching : " << mMaxReachHeight << EOL;

	os << TAB2 << "The Max WIDTH  reaching : " << mMaxReachWidth  << EOL;

	if( mDeadlockCount > 0 )
	{
		os << EOL_TAB2 << "The DEADLOCK found : " << mDeadlockCount << EOL;
	}
	if( mLivelockCount > 0 )
	{
		os << TAB2 << "The LIVELOCK found : " << mLivelockCount << EOL;
	}
	if( mStatementExitCount > 0 )
	{
		os << TAB2 << "The RUN#EXIT count : " << mStatementExitCount << EOL;
	}

	if( mStatementFatalErrorCount > 0 )
	{
		os << TAB2 << "The FATAL#ERROR count : "
				<< mStatementFatalErrorCount << EOL;
	}
	if( mSymbolicExecutionLimitationCount > 0 )
	{
		os << TAB2 << "The SYMB#LIMIT count  : "
				<< mSymbolicExecutionLimitationCount << EOL;
	}

	AvmCommunicationRdvPrimitive::reportGlobalStatistics( os );

	os << std::flush;
}

////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void MainProcessorUnit::tddRegressionReportImpl(OutStream & os)
{
//	os << TAB << "CONTEXT  count : "
//			<< ExecutionContextHeader::ID_NUMBER << EOL;

	os << TAB << "RUN STEP count : " << getSymbexDispatcher().getEvalNumber()
			<< EOL_FLUSH;
}


/**
 * EVAL TRACE
 */

static int EVAL_STEP_CURRENT_WIDTH   = 3;
static int NODE_COUNT_CURRENT_WIDTH  = 3;

static int NODE_HEIGHT_CURRENT_WIDTH = 3;
static int NODE_WIDTH_CURRENT_WIDTH  = 3;


static inline avm_size_t POW10( int n )
{
	switch( n )
	{
		case 3 : return( 1000     );
		case 4 : return( 10000    );
		case 5 : return( 100000   );
		case 6 : return( 1000000  );
		case 7 : return( 10000000 );
		default: return( static_cast<avm_size_t>( std::pow(10, n) ) );
	}
}


static inline std::string traceBound(avm_size_t limit, int width)
{
	std::ostringstream oss;
	if( limit < AVM_NUMERIC_MAX_SIZE_T )
	{
		( (limit < POW10(width))? oss << std::setw(width) : oss ) << limit;
	}
	else
	{
		oss << "+oo";
	}

	return( oss.str() );
}


void MainProcessorUnit::traceBoundEval(OutStream & os) const
{
	boost::format formatter(mBoundEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );

	os << TAB << formatter
			% traceBound(mEvalStepLimit  , EVAL_STEP_CURRENT_WIDTH)
			% traceBound(mNodeCountLimit , NODE_COUNT_CURRENT_WIDTH)
			% traceBound(mNodeHeightLimit, NODE_HEIGHT_CURRENT_WIDTH)
			% traceBound(mNodeWidthLimit , NODE_WIDTH_CURRENT_WIDTH)
			<< std::flush;
}


static inline std::string currentTrace(avm_size_t count, int & width)
{
	std::ostringstream oss;

	oss << std::setw( ( count < POW10(width) )? width : ++width ) << count;

	return( oss.str() );
}


//!! Warning: Unused static function
//static std::string traceElement(avm_size_t count, avm_size_t limit, int width)
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


void MainProcessorUnit::traceMinimumPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
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
