/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 28 nov. 2011
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "SymbexControllerUnitManager.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>

#include  <famcore/api/ProcessorUnitFactory.h>
#include  <famcore/api/ProcessorUnitRepository.h>

#include  <famcore/queue/ExecutionQueue.h>

#include <sew/SymbexEngine.h>


namespace sep
{


/**
 * GETTER
 * Configuration
 */
Configuration & SymbexControllerUnitManager::getConfiguration() const
{
	return( mSymbexEngine.getConfiguration() );
}

/**
 * GETTER
 * Builder
 */
Builder & SymbexControllerUnitManager::getBuilder()
{
	return( mSymbexEngine.getBuilder() );
}

/**
 * GETTER
 * AvmPrimitiveProcessor
 */
AvmPrimitiveProcessor & SymbexControllerUnitManager::getPrimitiveProcessor()
{
	return( mSymbexEngine.getPrimitiveProcessor() );
}


////////////////////////////////////////////////////////////////////////////////
// CONFIGURE  API
////////////////////////////////////////////////////////////////////////////////

bool SymbexControllerUnitManager::preConfigure()
{
	const WObject * theCONFIG = getParameterWObject();

	theCONFIG = Query::getRegexWSequence(theCONFIG,
				OR_WID2("manifest", "MANIFEST"), theCONFIG);

	if( theCONFIG != WObject::_NULL_ )
	{
		mAutoStart = Query::getRegexWPropertyBoolean(
				theCONFIG, CONS_WID2("auto", "start"), false);

		mAutoConfigure = Query::getRegexWPropertyBoolean(
				theCONFIG, CONS_WID2("auto", "conf(igure)?"), false);
	}

	return( mAutoConfigure || mAutoStart );
}

bool SymbexControllerUnitManager::configure()
{
	AVM_OS_LOG << _SEW_
			<< "< start > SymbexControllerUnitManager::configure ..."
			<< std::endl;

	mConfigFlag = RunnableElement::configure();

	if( preConfigure() )
	{
		//!! NOTHING
	}

	// Select MOE profile
	const WObject * moeProfile = Query::getRegexWSequence(
			getParameterWObject(), OR_WID2("moe", "MOE"));
	if( moeProfile == WObject::_NULL_ )
	{
		moeProfile = Query::getRegexWSequence(
				getParameterWObject(), OR_WID2("moc", "MOC"));
	}

	// A Possible Specific Profile
	const WObject * aProfile = Query::getRegexWPropertyWReference(
			moeProfile, OR_WID2("moe", "profile"), WObject::_NULL_);
	if( aProfile != WObject::_NULL_ )
	{
		const WObject * thePROPERTY = Query::getRegexWSequence(
				aProfile, OR_WID2("property", "PROPERTY"));
		if( thePROPERTY != WObject::_NULL_ )
		{
			moeProfile = thePROPERTY;
		}
		else
		{
			moeProfile = aProfile;
		}
	}

	mConfigFlag = ProcessorUnitFactory::configure(*this,
			getParameterWObject(), moeProfile)
			&& mConfigFlag;


AVM_IF_DEBUG_FLAG( CONFIGURING )
	AVM_OS_LOG << "The process configuration:> " << std::endl;
	toStream(AVM_OS_LOG);
AVM_ENDIF_DEBUG_FLAG( CONFIGURING )

	AVM_OS_LOG << _SEW_
			<< "< end > SymbexControllerUnitManager::configure ... done."
			<< std::endl;

	return mConfigFlag;
}


////////////////////////////////////////////////////////////////////////////////
// INIT / EXIT  API
////////////////////////////////////////////////////////////////////////////////

bool SymbexControllerUnitManager::initImpl()
{
	processorIt = mControllerUnits.begin();
	processorItEnd = mControllerUnits.end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePlugin() )
		{
			if( not (*processorIt)->init() )
			{
				AVM_OS_CLOG  << "Failed to init the PLUGIN PROCESSOR << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return true;
}

bool SymbexControllerUnitManager::exitImpl()
{
	processorIt = mControllerUnits.begin();
	processorItEnd = mControllerUnits.end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isEnablePlugin() )
		{
			if( not (*processorIt)->exit() )
			{
				AVM_OS_CLOG  << "Failed to exit the PLUGIN PROCESSOR << "
						<< ( *processorIt)->getParameterWObject()
								->getFullyQualifiedNameID()
						<< " >> " << std::endl;

				return( false );
			}
		}
	}

	return( true );
}

////////////////////////////////////////////////////////////////////////////////
// ( PRE / POST ) PROCESS  API
////////////////////////////////////////////////////////////////////////////////

bool SymbexControllerUnitManager::preprocess()
{
AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPreprocessingInitialize() )
	mMainProcessor.debugPreprocessingInitialize();
AVM_ENDIF_DEBUG_ENABLED_AND

	bool isOK = mMainProcessor.preprocess();

	if( isOK )
	{
		isOK = mPreprocessorControllerUnits.preprocess();
	}

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPreprocessingFinalize() )
	mMainProcessor.debugPreprocessingFinalize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}


bool SymbexControllerUnitManager::postprocess()
{
AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPostprocessingInitialize() )
	mMainProcessor.debugPostprocessingInitialize();
AVM_ENDIF_DEBUG_ENABLED_AND

	bool isOK = mMainProcessor.postprocess();

	if( isOK )
	{
		isOK = mPostprocessorControllerUnits.postprocess();
	}

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPostprocessingFinalize() )
	mMainProcessor.debugPostprocessingFinalize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}



////////////////////////////////////////////////////////////////////////////////
// FILTERING  API
////////////////////////////////////////////////////////////////////////////////

bool SymbexControllerUnitManager::filteringInitialize()
{
	bool isOK = true;

	processorIt = mControllerUnits.begin();
	processorItEnd = mControllerUnits.end();
	for(  ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isWeakEnableFilter() )
		{
			if( not (*processorIt)->filteringInitialize() )
			{
				isOK = false;

				break;
			}
		}
	}

//	if( mMainProcessor.filteringInitialize() )
//	{
//		return( mPrefilterControllerUnits.filteringInitialize() );
//	}
//
//	return( false );

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugFilteringInitialize() )
	mMainProcessor.debugFilteringInitialize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}


bool SymbexControllerUnitManager::filteringFinalize()
{
	bool isOK = true;

	processorIt = mControllerUnits.begin();
	processorItEnd = mControllerUnits.end();
	for( ; processorIt != processorItEnd ; ++processorIt )
	{
		if( (*processorIt)->isWeakEnableFilter() )
		{
			if( not (*processorIt)->filteringFinalize() )
			{
				isOK = false;

				break;
			}
		}
	}

//	if( mMainProcessor.filteringFinalize() )
//	{
//		return( mPrefilterControllerUnits.filteringFinalize() );
//	}
//
//	return( false );

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugFilteringFinalize() )
	mMainProcessor.debugFilteringFinalize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}


////////////////////////////////////////////////////////////////////////////////
// ( PRE / POST ) FILTER  API
////////////////////////////////////////////////////////////////////////////////

bool SymbexControllerUnitManager::prefilter()
{
AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPrefiltering() )
	mMainProcessor.debugPrefiltering();
AVM_ENDIF_DEBUG_ENABLED_AND

	if( mMainProcessor.prefilter() )
	{
		if( mRedundancyProcessor.prefilter() )
		{
			return( mPrefilterControllerUnits.prefilter() );
		}
	}

	return( false );
}


bool SymbexControllerUnitManager::finalizePrefiltering()
{
	bool isOK = mMainProcessor.finalizePrefiltering();

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPrefilteringFinalize() )
	mMainProcessor.debugPrefilteringFinalize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}


bool SymbexControllerUnitManager::postfilter()
{
AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPostfiltering() )
	mMainProcessor.debugPostfiltering();
AVM_ENDIF_DEBUG_ENABLED_AND

	if( mMainProcessor.postfilter() )
	{
		return( mPostfilterControllerUnits.postfilter() );
	}

	return( false );
}


bool SymbexControllerUnitManager::finalizePostfiltering()
{
	bool isOK = mMainProcessor.finalizePostfiltering();

//	if( mMainProcessor.finalizePostfiltering() )
//	{
//		return( mPostfilterControllerUnits.finalizePostfiltering() );
//	}
//
//	return( false );

AVM_IF_DEBUG_ENABLED_AND( mMainProcessor.isDebugPostfilteringFinalize() )
	mMainProcessor.debugPostfilteringFinalize();
AVM_ENDIF_DEBUG_ENABLED_AND

	return( isOK );
}


////////////////////////////////////////////////////////////////////////////////
// REPORT  API
////////////////////////////////////////////////////////////////////////////////

void SymbexControllerUnitManager::report(OutStream & os) const
{
	os << TAB << "REPORT" << EOL_INCR_INDENT;

	mQueueProcessor.report(os);
	os << std::flush;

	mMainProcessor.report(os);
	os << std::flush;

	mRedundancyProcessor.report(os);
	os << std::flush;

	for( const auto & itProcessor : mControllerUnits )
	{
		if( itProcessor->isEnablePlugin() )
		{
			itProcessor->report(os);
			os << std::flush;
		}
	}

	os << DECR_INDENT << std::flush;
}


/**
 * EVAL TRACE
 */
void SymbexControllerUnitManager::traceBoundEval(OutStream & os) const
{
	mMainProcessor.traceBoundEval(os);
}

void SymbexControllerUnitManager::traceInitSpider(OutStream & os) const
{
	mMainProcessor.traceInitSpider(os);
}

void SymbexControllerUnitManager::traceStepSpider(
		OutStream & os, const ExecutionContext & anEC) const
{
	mMainProcessor.traceStepSpider(os, anEC);
}

void SymbexControllerUnitManager::traceStopSpider(OutStream & os) const
{
	mMainProcessor.traceStopSpider(os);
}

void SymbexControllerUnitManager::tracePreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	mMainProcessor.tracePreEval(os, anEC);
	os << std::flush;

	AVM_VERBOSITY_IF_ISNOT_MINIMUM
		for( const auto & itProcessor : mControllerUnits )
		{
			if( itProcessor->isEnablePlugin() &&
				itProcessor->isLifecycleRunnable() )
			{
				itProcessor->tracePreEval(os, anEC);
			}
		}
	AVM_VERBOSITY_ENDIF
}


void SymbexControllerUnitManager::tracePostEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	mMainProcessor.tracePostEval(os, anEC);
	os << std::flush;

	for( const auto & itProcessor : mControllerUnits )
	{
		if( itProcessor->isEnablePlugin() &&
			itProcessor->isLifecycleRunnable() )
		{
			itProcessor->tracePostEval(os, anEC);
		}
	}
}


void SymbexControllerUnitManager::reportEval(OutStream & os) const
{
	mMainProcessor.reportEval(os);
}


////////////////////////////////////////////////////////////////////////////////
// UNIT TEST API
////////////////////////////////////////////////////////////////////////////////

void SymbexControllerUnitManager::tddUnitReport(OutStream & os) const
{
	mMainProcessor.tddUnitReport(os);

	for( const auto & itProcessor : mControllerUnits )
	{
		if( itProcessor->isEnablePlugin() )
		{
			itProcessor->tddUnitReport(os);
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// NON-REGRESSION TEST API
////////////////////////////////////////////////////////////////////////////////

void SymbexControllerUnitManager::tddRegressionReport(OutStream & os) const
{
	mMainProcessor.tddRegressionReport(os);

	for( const auto & itProcessor : mControllerUnits )
	{
		if( itProcessor->isEnablePlugin() )
		{
			itProcessor->tddRegressionReport(os);
		}
	}
}


////////////////////////////////////////////////////////////////////////////////
// SERIALIZATION API
////////////////////////////////////////////////////////////////////////////////

void SymbexControllerUnitManager::toStream(OutStream & os) const
{
//	if( mParameterWObject != nullptr )
//	{
//		mParameterWObject->toStream(os);
//	}

	os << TAB << "moe:" << EOL_INCR_INDENT;

	os << TAB << "supervisor = " << mMainProcessor.strUniqId()  << ";" << EOL;

	os << TAB << "queue = " << mQueueProcessor.strUniqId() << ";" << EOL;

	os << TAB << "redundancy = " << mRedundancyProcessor.strUniqId() << ";"
			<< EOL2;

	mPreprocessorControllerUnits.toStream(os, "pre_processor = " );

	os << EOL;

	mPrefilterControllerUnits.toStream(os, "pre_filter = " );

	mPostfilterControllerUnits.toStream(os, "post_filter = " );

	os << EOL;

	mPostprocessorControllerUnits.toStream(os, "post_processor = " );

	os << DECR_INDENT;

}

} /* namespace sep */
