/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 27 janv. 2015
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AvmDebugProcessor.h"


namespace sep
{


////////////////////////////////////////////////////////////////////////////////
// REPORT API
////////////////////////////////////////////////////////////////////////////////

void AvmDebugProcessor::reportMinimum(OutStream & os) const
{
	reportHeader(os, "DEBUGGER ");

	os << std::flush;
}


void AvmDebugProcessor::reportDefault(OutStream & os) const
{
	reportHeader(os, "DEBUGGER ");

	os << std::flush;
}


bool AvmDebugProcessor::configureImpl()
{
	return( IDebugProcessorProvider::debugConfigureImpl( getParameterWObject() ) );
}


////////////////////////////////////////////////////////////////////////////////
// PROCESS API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::preprocess()
{
	if( mDebugPreprocessingFlag )
	{
		mDebugPromptPrefix = "PRE-PROCESSING";

		return( IDebugProcessorProvider::debugPreprocessing() );
	}

	return true;
}

bool AvmDebugProcessor::postprocess()
{
	if( mDebugPostprocessingFlag )
	{
		mDebugPromptPrefix = "POST-PROCESSING";

		return( IDebugProcessorProvider::debugPostprocessing() );
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// INITIALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::filteringInitialize()
{
	if( mDebugFilteringInitializeFlag )
	{
		return( IDebugProcessorProvider::debugFilteringInitialize() );
	}

	return true;
}

bool AvmDebugProcessor::filteringInitialize(ExecutionContext * anEC)
{
	if( mDebugFilteringDetailFlag )
	{
		return( IDebugProcessorProvider::debugFilteringInitialize(anEC) );
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// FINALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::finalizeFiltering()
{
	if( mDebugFilteringFinalizeFlag )
	{
		return( IDebugProcessorProvider::debugFilteringFinalize() );
	}

	return true;
}

bool AvmDebugProcessor::finalizeFiltering(ExecutionContext * anEC)
{
	if( mDebugFilteringDetailFlag )
	{
		return( IDebugProcessorProvider::debugFilteringFinalize(anEC) );
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::prefilter()
{
	if( mDebugPrefilteringFlag )
	{
		return( IDebugProcessorProvider::debugPrefiltering() );
	}

	return true;
}

bool AvmDebugProcessor::prefilter(ExecutionContext & anEC)
{
	if( mDebugPrefilteringDetailFlag )
	{
		return( IDebugProcessorProvider::debugPrefiltering(& anEC) );
	}

	return true;
}


bool AvmDebugProcessor::finalizePrefiltering()
{
	if( mDebugFilteringFinalizeFlag )
	{
		return( IDebugProcessorProvider::debugPrefilteringFinalize() );
	}

	return true;
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::postfilter()
{
	if( mDebugPostfilteringFlag )
	{
		return( IDebugProcessorProvider::debugPostfiltering() );
	}

	return true;
}


bool AvmDebugProcessor::postfilter(ExecutionContext & anEC)
{
	if( mDebugPostfilteringDetailFlag)
	{
		return( IDebugProcessorProvider::debugPostfiltering(& anEC) );
	}

	return true;
}


bool AvmDebugProcessor::finalizePostfiltering()
{
	if( mDebugPostfilteringFinalizeFlag )
	{
		return( IDebugProcessorProvider::debugPostfilteringFinalize() );
	}

	return true;
}


} /* namespace sep */
