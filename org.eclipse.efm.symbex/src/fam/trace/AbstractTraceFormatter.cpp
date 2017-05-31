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

bool AbstractTraceFormatter::configure(WObject * wfParameterObject)
{
	WObject * thePROPERTY = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("property", "PROPERTY"));

	if( thePROPERTY != WObject::_NULL_ )
	{
		mPrintLifelines = Query::getRegexWPropertyBoolean(
			thePROPERTY, CONS_WID2("print", "lifelines"), false);
	}

	WObject * theFORMAT = Query::getRegexWSequence(
			wfParameterObject, OR_WID2("format", "FORMAT"));

	if( theFORMAT == WObject::_NULL_ ) {
		theFORMAT = Query::getRegexWSequence(wfParameterObject,
				OR_WID2("property", "PROPERTY"), wfParameterObject);
	}

	if( theFORMAT != WObject::_NULL_ )
	{
		mWrapData.LINE_WIDTH = Query::getRegexWPropertyPosSizeT(
				theFORMAT, CONS_WID3("line", "wrap", "width"),
				DEFAULT_WRAP_DATA.LINE_WIDTH);

		mWrapData.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
			CONS_WID3("line", "wrap", "separator"), mWrapData.SEPARATOR);
		StringTools::replaceAll(mWrapData.SEPARATOR, "\\t" , "\t");
		StringTools::replaceAll(mWrapData.SEPARATOR, "\\n" , "\n");

		mMultiValueArrayCSS.BEGIN = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "array", "begin"), "[ ");
		mMultiValueArrayCSS.SEPARATOR = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "array", "separator"), " , ");
		mMultiValueArrayCSS.END = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "array", "end"), " ]");

		mMultiValueParamsCSS.BEGIN = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "begin"), "( ");
		mMultiValueParamsCSS.SEPARATOR = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "separator"), " , ");
		mMultiValueParamsCSS.END = Query::getRegexWPropertyString(theFORMAT,
				CONS_WID3("value", "param(eter)?s?", "end"), " )");

		mMultiValueStructCSS.BEGIN = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "struct", "begin"), "{ ");
		mMultiValueStructCSS.SEPARATOR = Query::getRegexWPropertyString(
			theFORMAT, CONS_WID3("value", "struct", "separator"), " , ");
		mMultiValueStructCSS.END = Query::getRegexWPropertyString(
				theFORMAT, CONS_WID3("value", "struct", "end"), " }");
	}

	return( configureImpl(wfParameterObject) );
}



} /* namespace sep */
