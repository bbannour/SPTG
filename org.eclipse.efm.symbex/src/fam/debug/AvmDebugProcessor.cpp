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

#include <boost/format.hpp>


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
	return( IDebugProcessorProvider::debugPreprocessing() );
}

bool AvmDebugProcessor::postprocess()
{
	return( IDebugProcessorProvider::debugPostprocessing() );
}


////////////////////////////////////////////////////////////////////////////////
// INITIALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::filteringInitialize()
{
	return( IDebugProcessorProvider::debugFilteringInitialize() );
}

bool AvmDebugProcessor::filteringInitialize(ExecutionContext * anEC)
{
	return( IDebugProcessorProvider::debugFilteringInitialize(anEC) );
}


////////////////////////////////////////////////////////////////////////////////
// FINALIZE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::finalizeFiltering()
{
	return( IDebugProcessorProvider::debugFilteringFinalize() );
}

bool AvmDebugProcessor::finalizeFiltering(ExecutionContext * anEC)
{
	return( IDebugProcessorProvider::debugFilteringFinalize(anEC) );
}


////////////////////////////////////////////////////////////////////////////////
// PRE-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::prefilter()
{
	return( IDebugProcessorProvider::debugPrefiltering() );
}

bool AvmDebugProcessor::prefilter(ExecutionContext & anEC)
{
	return( IDebugProcessorProvider::debugPrefiltering(& anEC) );
}


bool AvmDebugProcessor::finalizePrefiltering()
{
	return( IDebugProcessorProvider::debugPrefilteringFinalize() );
}


////////////////////////////////////////////////////////////////////////////////
// POST-FILTER API
////////////////////////////////////////////////////////////////////////////////

bool AvmDebugProcessor::postfilter()
{
	return( IDebugProcessorProvider::debugPostfiltering() );
}


bool AvmDebugProcessor::postfilter(ExecutionContext & anEC)
{
	return( IDebugProcessorProvider::debugPostfiltering(& anEC) );
}


bool AvmDebugProcessor::finalizePostfiltering()
{
	return( IDebugProcessorProvider::debugPostfilteringFinalize() );
}


/**
 * EVAL TRACE
 */

void AvmDebugProcessor::traceMinimumPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	boost::format formatter(mPreEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );
}


void AvmDebugProcessor::traceDefaultPreEval(
		OutStream & os, const ExecutionContext & anEC) const
{
//	os << TAB << "E[" << std::setw(4) << anEC->getEvalNumber() << "] "
//			<< anEC->str_min() << EOL_FLUSH;
}


void AvmDebugProcessor::traceMinimumPostEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	//!! NOTHING
}

void AvmDebugProcessor::traceDefaultPostEval(
		OutStream & os, const ExecutionContext & anEC) const
{
	//!! NOTHING
}



void AvmDebugProcessor::reportEval(OutStream & os) const
{
	boost::format formatter(mReportEvalTraceFormatter);
	formatter.exceptions( boost::io::no_error_bits );

//	formatter.exceptions( boost::io::all_error_bits ^
//			( boost::io::too_many_args_bit | boost::io::too_few_args_bit ) );
}



} /* namespace sep */
