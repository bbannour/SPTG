/*******************************************************************************
 * Copyright (c) 2016 CEA LIST.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Created on: 6 janv. 2014
 *
 * Contributors:
 *  Arnault Lapitre (CEA LIST) arnault.lapitre@cea.fr
 *   - Initial API and implementation
 ******************************************************************************/

#include "AbstractTraceFormatter.h"

#include "SequenceDiagramTraceBuilder.h"
#include "AvmTraceGenerator.h"

#include <fml/workflow/Query.h>
#include <fml/workflow/WObject.h>


namespace sep
{

/*
prototype process::trace_generator as &avm::processor.TRACE_GENERATOR is
 ...

 section FORMAT
  ...
  @line#wrap#width     = 80;
  @line#wrap#separator = "\n\t";
  ...
  @value#array#begin = "[ ";
  @value#array#separator = " , ";
  @value#array#end = " ]";

  @value#struct#begin = "{ ";
  @value#struct#separator = " , ";
  @value#struct#end = " }";
  ...
 endsection FORMAT

 ...

endprototype
*/

bool AbstractTraceFormatter::configure(const WObject * wfParameterObject)
{
	const WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mPrintLifelines = Query::getRegexWPropertyBoolean(
			thePROPERTY, CONS_WID2("print", "lifelines"), false);
	}
	else
	{
		mPrintLifelines = false;
	}

	const WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));

	if( theFORMAT == WObject::_NULL_ ) {
		theFORMAT = Query::getRegexWSequence(wfParameterObject,
				OR_WID2("property", "PROPERTY"), wfParameterObject);
	}

	if( theFORMAT != WObject::_NULL_ )
	{
		if( not mMultiValueArrayCSS.configure(theFORMAT,
				"array", DEFAULT_SYMBEX_VALUE_ARRAY_CSS) )
		{
			//!!NOTHING
		}

		if( not mMultiValueParamsCSS.configure(theFORMAT,
				"param(eter)?s?", DEFAULT_SYMBEX_VALUE_PARAMS_CSS) )
		{
			//!!NOTHING
		}

		if( not mMultiValueStructCSS.configure(theFORMAT,
				"struct", DEFAULT_SYMBEX_VALUE_STRUCT_CSS) )
		{
			//!!NOTHING
		}
	}

	return( configureImpl(wfParameterObject) );
}


////////////////////////////////////////////////////////////////////////////
// FORMAT API
////////////////////////////////////////////////////////////////////////////

void AbstractTraceFormatter::format(TraceManager & aTraceManager)
{
	formatOneFile(aTraceManager);

	if( mTraceGenerator.getTraceBuilder().isOneTracePerfile() )
	{
		formatOnePathPerFile(aTraceManager);
	}
}

void AbstractTraceFormatter::formatOneFile(TraceManager & aTraceManager)
{
	mTraceGenerator.beginStream();
	while( mTraceGenerator.hasStream() )
	{
AVM_IF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )
		mTraceGenerator.currentStream() << "format:> ";
		mTraceGenerator.getTraceFilter().toStream(mTraceGenerator.currentStream());
		mTraceGenerator.currentStream() << std::endl;

		aTraceManager.toStream( mTraceGenerator.currentStream() );
AVM_ENDIF_DEBUG_LEVEL_FLAG2( MEDIUM , PROCESSOR , TRACE )

		formatOneFile(mTraceGenerator.currentStream(), aTraceManager);
	}

	mTraceGenerator.closeStream();
}


void AbstractTraceFormatter::formatOneFile(
		OutStream & os, TraceManager & aTraceManager)
{
	os.setSymbexValueCSS(mMultiValueArrayCSS,
			mMultiValueParamsCSS, mMultiValueStructCSS);

	formatHeader(os);

	for( const auto & itTraceElement : aTraceManager )
	{
		formatTrace(os, * itTraceElement);
	}

	formatFooter(os);

	os.restoreSymbexValueCSS();
}


void AbstractTraceFormatter::formatOnePathPerFile(
		TraceManager & aTraceManager)
{
	for( const auto & itTraceElement : aTraceManager )
	{
		OutStream & os = mTraceGenerator.newFileStream(itTraceElement->tid);

		os.setSymbexValueCSS(mMultiValueArrayCSS,
				mMultiValueParamsCSS, mMultiValueStructCSS);

		formatHeader(os);

		formatTrace(os, * itTraceElement);

		formatFooter(os);

		os.restoreSymbexValueCSS();
	}
}


} /* namespace sep */
